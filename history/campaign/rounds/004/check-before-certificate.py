import argparse
import itertools
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


def algebraic(text):
    a = z3.Real('value')
    exprs = z3.parse_smt2_string('(assert (= value '+text+'))', decls={'value': a})
    assert len(exprs) == 1 and z3.is_eq(exprs[0]) and exprs[0].arg(0).eq(a)
    value = z3.simplify(exprs[0].arg(1))
    assert z3.is_rational_value(value) or z3.is_algebraic_value(value)
    return value


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
    out = {name:[[model.eval(x,model_completion=True).sexpr() for x in row] for row in mat] for name,mat in [('W',W),('H',H)]}
    assert target_valid(t,out)
    return out


def run_candidate(path,s):
    p = subprocess.run(['python3',str(path)],input=json.dumps(s),text=True,capture_output=True,check=True)
    t = json.loads(p.stdout)
    expected = source_solve(s) is not None
    witness = target_solve(t)
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
    root='(root-obj (+ (^ x 2) (- 2)) 2)'
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
