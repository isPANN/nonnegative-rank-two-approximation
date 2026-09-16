import argparse
import itertools
import math
import json
import subprocess
from fractions import Fraction
from pathlib import Path
import z3


def rat(value):
    if not isinstance(value, (str, int)) or isinstance(value, bool):
        raise ValueError('Expected a rational string or integer')
    return Fraction(value)


def legal_source(s):
    n = len(s['variables'])
    assert s['variables'] == list(range(n))
    assert all(len(c) <= 3 and all(type(x) is int and 1 <= abs(x) <= n for x in c) for c in s['clauses'])


def source_valid(s, a):
    legal_source(s)
    return len(a) == len(s['variables']) and all(type(x) is bool for x in a) and all(any(a[abs(x)-1] == (x > 0) for x in c) for c in s['clauses'])


def source_solve(s):
    legal_source(s)
    v = [z3.Bool(f'b{i}') for i in s['variables']]
    solver = z3.Solver()
    solver.add(*[z3.Or(*[v[abs(x)-1] if x > 0 else z3.Not(v[abs(x)-1]) for x in c]) for c in s['clauses']])
    status = solver.check()
    assert status in (z3.sat, z3.unsat), status
    if status == z3.unsat:
        return None
    a = [z3.is_true(solver.model().eval(x, model_completion=True)) for x in v]
    assert source_valid(s, a)
    return a


def target_data(t):
    X = [[rat(x) for x in row] for row in t['X']]
    assert X and X[0] and all(len(row) == len(X[0]) for row in X)
    tau = rat(t['tau'])
    assert tau >= 0 and all(x >= 0 for row in X for x in row)
    return X, tau


def real(x):
    return z3.RealVal(str(x))


def encode(v):
    if z3.is_rational_value(v):return str(Fraction(v.numerator_as_long(),v.denominator_as_long()))
    assert z3.is_algebraic_value(v)
    return {'poly':[x.as_long() for x in v.poly()], 'root':v.index()}


def algebraic(value):
    if isinstance(value,str):return real(rat(value))
    assert type(value) is dict and type(value['poly']) is list and value['poly'] and value['poly'][-1]!=0
    assert all(type(c) is int for c in value['poly']) and type(value['root']) is int and value['root']>0
    terms=' '.join(f'(* {c if c>=0 else "(- "+str(-c)+")"} (^ x {i}))' for i,c in enumerate(value['poly']))
    text=f'(root-obj (+ {terms}) {value["root"]})'
    a=z3.Real('value')
    exprs=z3.parse_smt2_string('(assert (= value '+text+'))',decls={'value':a})
    result=z3.simplify(exprs[0].arg(1))
    assert z3.is_algebraic_value(result) or z3.is_rational_value(result)
    return result


def target_valid(t, witness):
    X, tau = target_data(t)
    W = [[algebraic(x) for x in row] for row in witness['W']]
    H = [[algebraic(x) for x in row] for row in witness['H']]
    if len(W) != len(X) or any(len(r) != 2 for r in W) or len(H) != 2 or any(len(r) != len(X[0]) for r in H):
        return False
    if not all(z3.is_true(z3.simplify(x >= 0)) for row in W+H for x in row):
        return False
    loss = z3.simplify(sum((real(X[i][j])-sum(W[i][k]*H[k][j] for k in range(2)))**2 for i in range(len(X)) for j in range(len(X[0]))))
    return z3.is_true(z3.simplify(loss <= real(tau)))


def target_solve(t):
    X, tau = target_data(t)
    m,n = len(X),len(X[0])
    W = [[z3.Real(f'w{i}_{k}') for k in range(2)] for i in range(m)]
    H = [[z3.Real(f'h{k}_{j}') for j in range(n)] for k in range(2)]
    Y = [[z3.Real(f'y{i}_{j}') for j in range(n)] for i in range(m)]
    solver = z3.SolverFor('QF_NRA')
    solver.add(*[x >= 0 for row in Y for x in row])
    for rows in itertools.combinations(range(m),3):
        for cols in itertools.combinations(range(n),3):
            a,b,c=rows;d,e,f=cols
            solver.add(Y[a][d]*(Y[b][e]*Y[c][f]-Y[b][f]*Y[c][e])-Y[a][e]*(Y[b][d]*Y[c][f]-Y[b][f]*Y[c][d])+Y[a][f]*(Y[b][d]*Y[c][e]-Y[b][e]*Y[c][d])==0)
    solver.add(sum((real(X[i][j])-Y[i][j])**2 for i in range(m) for j in range(n)) <= real(tau))
    status = solver.check()
    assert status in (z3.sat,z3.unsat), (status,solver.reason_unknown())
    if status == z3.unsat:
        return None
    product = [[solver.model().eval(x,model_completion=True) for x in row] for row in Y]
    factors = z3.SolverFor('QF_NRA')
    factors.add(*[x >= 0 for row in W+H for x in row])
    factors.add(*[sum(W[i][k]*H[k][j] for k in range(2))==product[i][j] for i in range(m) for j in range(n)])
    assert factors.check()==z3.sat, 'A nonnegative matrix of rank at most two must factor'
    model = factors.model()
    out = {name:[[encode(model.eval(x,model_completion=True)) for x in row] for row in mat] for name,mat in [('W',W),('H',H)]}
    assert target_valid(t,out)
    return out


def certified_target(t):
    X,tau=target_data(t);n=len(X)
    assert n>=3 and all(len(r)==n for r in X)
    epsilon=min(X[i][j] for i in range(n) for j in range(i))
    residual=[[X[i][j]-int(i==j)-epsilon for j in range(n)] for i in range(n)]
    denom=math.lcm(*(x.denominator for row in residual for x in row))
    numerator=math.gcd(*(int(x*denom) for row in residual for x in row))
    delta=Fraction(numerator,denom);assert delta>0 and epsilon>0
    A=[[x/delta for x in row] for row in residual]
    assert all(x.denominator==1 and x>=0 for row in A for x in row)
    A=[[int(x) for x in row] for row in A]
    assert all(A[i][j]==A[j][i] for i in range(n) for j in range(n))
    d=sum(A[0]);assert all(sum(row)==d for row in A)
    L=1+n+sum(map(sum,A))+2*d+n*(max(map(max,A))+1)
    norm=sum(x*x for row in A for x in row)
    assert 0<=tau<=n-2+2*delta*L+delta*delta*norm and delta*L<=1 and epsilon*n<=1
    eta=4*n*delta*L
    assert eta<1 and eta<2*epsilon*n+epsilon*epsilon*n*n
    assert 9*eta/(epsilon*n)<=epsilon*epsilon
    rn=math.isqrt(epsilon.numerator);rd=math.isqrt(epsilon.denominator)
    assert rn*rn==epsilon.numerator and rd*rd==epsilon.denominator
    radius=epsilon+8*n*Fraction(rn,rd);assert radius<Fraction(1,2*n)
    cutoff=((tau-(n-2)-delta*delta*norm)/(2*delta)-sum(A[i][i] for i in range(n))+2*d)/n
    relaxed=cutoff+L*radius/n
    cap=max(A[i][j] for i in range(n) for j in range(i))
    edges=[(i,j,cap-A[i][j]) for i in range(n) for j in range(i) if cap!=A[i][j]]
    for size in range(1,n//2+1):
        b=[z3.Bool(f'cut{i}') for i in range(n)]
        solver=z3.Solver();solver.add(z3.PbEq([(x,1) for x in b],size))
        bound=math.floor(relaxed*size*(n-size))
        solver.add(z3.PbGe([(z3.Xor(b[i],b[j]),w) for i,j,w in edges],cap*size*(n-size)-bound))
        status=solver.check();assert status in (z3.sat,z3.unsat)
        if status==z3.unsat:continue
        S={i for i,x in enumerate(b) if z3.is_true(solver.model().eval(x,model_completion=True))}
        weight=cap*size*(n-size)-sum(w for i,j,w in edges if (i in S)!=(j in S))
        assert Fraction(weight,size*(n-size))<=cutoff, 'Certificate inconclusive: boundary band needs general real solving'
        W=[[str(int(i in S)),str(int(i not in S))] for i in range(n)]
        H=[[str(epsilon+(Fraction(1,size) if j in S else 0)) for j in range(n)], [str(epsilon+(Fraction(1,n-size) if j not in S else 0)) for j in range(n)]]
        witness={'W':W,'H':H};assert target_valid(t,witness)
        return witness
    return None


def run_candidate(path,s):
    p = subprocess.run(['python3',str(path)],input=json.dumps(s),text=True,capture_output=True,check=True)
    t = json.loads(p.stdout)
    expected = source_solve(s) is not None
    witness = certified_target(t) if len(t['X'])>3 else target_solve(t)
    assert (witness is not None) == expected, {'source':s,'target':t,'expected':expected}
    calls = 0
    if witness is not None:
        other = {'W':[list(reversed(row)) for row in witness['W']], 'H':list(reversed(witness['H']))}
        for w in [witness,other]:
            assert target_valid(t,w)
            p = subprocess.run(['python3',str(path),'--extract'],input=json.dumps({'source':s,'target_solution':w}),text=True,capture_output=True,check=True)
            assert source_valid(s,json.loads(p.stdout)), 'Invalid source recovery'
            calls += 1
    return {'source':s,'target':t,'yes':expected,'witness':witness,'recovery_calls':calls}


def self_test():
    cases = json.loads(Path(__file__).with_name('cases.json').read_text())
    for c in cases:
        s=c['source']; a=source_solve(s)
        brute=any(source_valid(s,list(v)) for v in itertools.product([False,True],repeat=len(s['variables'])))
        assert brute == c['yes'] == (a is not None)
    targets = [({'X':[[0]],'tau':0},True),({'X':[[1,2],[3,4]],'tau':0},True),({'X':[[1,0,0],[0,1,0],[0,0,1]],'tau':0},False)]
    for t,expected in targets:
        w=target_solve(t);assert (w is not None)==expected
        print(json.dumps({'target':t,'yes':expected,'witness':w}),flush=True)
    root={'poly':[-2,0,1],'root':2}
    witness={'W':[[root,'0']],'H':[[root],['0']]}
    assert target_valid({'X':[[2]],'tau':0},witness)
    assert not target_valid({'X':[[1]],'tau':0},witness)
    assert not target_valid({'X':[[1]],'tau':0},{'W':[['-1','0']],'H':[['-1'],['0']]})
    assert not source_valid(cases[1]['source'],[False])
    print(json.dumps({'source_cases':len(cases),'target_cases':len(targets),'algebraic_and_negative_witness_regressions':'pass','z3':z3.get_version_string()}),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--self-test',action='store_true');p.add_argument('--candidate',type=Path);args=p.parse_args()
    if args.self_test:self_test()
    elif args.candidate:
        for c in json.loads(Path(__file__).with_name('cases.json').read_text()):
            print(json.dumps(run_candidate(args.candidate,c['source'])),flush=True)
    else:p.error('Choose --self-test or --candidate')
