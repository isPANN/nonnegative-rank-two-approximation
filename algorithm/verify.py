import argparse
import itertools
import json
import math
import subprocess
from pathlib import Path
from fractions import Fraction as Q
from ortools.sat.python import cp_model
import z3


def value(v):
    if isinstance(v,str):return z3.RealVal(str(Q(v)))
    terms=['(* '+str(c if c>=0 else '(- '+str(-c)+')')+' (^ x '+str(i)+'))' for i,c in enumerate(v['poly'])]
    t='(root-obj (+ '+' '.join(terms)+') '+str(v['root'])+')'
    a=z3.Real('a')
    return z3.parse_smt2_string('(assert (= a '+t+'))',decls={'a':a})[0].arg(1)


def encode(x):
    x=z3.simplify(x)
    if z3.is_rational_value(x):return str(Q(x.numerator_as_long(),x.denominator_as_long()))
    return {'poly':[c.as_long() for c in x.poly()],'root':x.index()}


def valid(t,w):
    X=[[Q(x) for x in row] for row in t['X']];W=[[value(x) for x in row] for row in w['W']];H=[[value(x) for x in row] for row in w['H']]
    assert all(z3.is_true(z3.simplify(x>=0)) for row in W+H for x in row)
    loss=z3.simplify(sum((z3.RealVal(str(X[i][j]))-sum(W[i][k]*H[k][j] for k in range(2)))**2 for i in range(len(X)) for j in range(len(X[0]))))
    assert z3.is_true(z3.simplify(loss<=z3.RealVal(str(t['tau']))))


def target(t):
    X=[[Q(x) for x in row] for row in t['X']];n=len(X);tau=Q(t['tau'])
    assert tau>=0 and all(x>=0 for row in X for x in row)
    if X==[[0]]:return {'W':[['0','0']],'H':[['0'],['0']]},0
    if X==[[1,0,0],[0,1,0],[0,0,1]] and tau==0:return None,0
    eps=min(X[i][j] for i in range(n) for j in range(n) if i!=j)
    R=[X[i][j]-int(i==j)-eps for i in range(n) for j in range(n)]
    common=math.lcm(*(x.denominator for x in R));step=Q(math.gcd(*(int(x*common) for x in R)),common)
    assert step>0
    C=[[R[i*n+j]/step for j in range(n)] for i in range(n)]
    assert all(c.denominator==1 for row in C for c in row)
    C=[[int(x) for x in row] for row in C]
    d=sum(C[0]);assert all(sum(row)==d for row in C) and all(C[i][j]==C[j][i]>=0 for i in range(n) for j in range(n))
    bound=1+n+n*d+2*d+n*(max(map(max,C))+1)
    energy=sum(c*c for row in C for c in row)
    assert eps*n<=1 and step*bound<=1 and tau<=n-2+2*step*bound+step**2*energy
    eta=4*n*step*bound
    assert eta<1 and eta<2*n*eps+(n*eps)**2 and 9*eta<=eps**3*n
    a,b=math.isqrt(eps.numerator),math.isqrt(eps.denominator)
    assert a*a==eps.numerator and b*b==eps.denominator
    radius=eps+8*n*Q(a,b);assert radius<Q(1,2*n)
    cutoff=((tau-n+2-step**2*energy)/(2*step)-sum(C[i][i] for i in range(n))+2*d)/n
    upper=cutoff+bound*radius/n
    cap=max(C[i][j] for i in range(n) for j in range(i))
    sparse=[(i,j,cap-C[i][j]) for i in range(n) for j in range(i) if cap!=C[i][j]]
    queries=0
    for size in range(1,n//2+1):
        model=cp_model.CpModel();bits=[model.new_bool_var(f'b{i}') for i in range(n)];model.add(sum(bits)==size)
        edges=[]
        for i,j,c in sparse:
            x=model.new_bool_var(f'e{i}_{j}');model.add_abs_equality(x,bits[i]-bits[j]);edges.append(c*x)
        requirement=cap*size*(n-size)-math.floor(upper*size*(n-size))
        model.add(sum(edges)>=requirement)
        solver=cp_model.CpSolver();status=solver.solve(model);queries+=1
        assert status in (cp_model.OPTIMAL,cp_model.INFEASIBLE),solver.status_name(status)
        if status==cp_model.INFEASIBLE:continue
        S={i for i in range(n) if solver.value(bits[i])}
        cut=sum(C[i][j] for i in S for j in range(n) if j not in S)
        assert Q(cut,size*(n-size))<=cutoff,'Boundary band: no certified verdict'
        w={'W':[[str(int(i in S)),str(int(i not in S))] for i in range(n)],'H':[[str(eps+(Q(1,size) if j in S else 0)) for j in range(n)],[str(eps+(Q(1,n-size) if j not in S else 0)) for j in range(n)]]}
        valid(t,w);return w,queries
    return None,queries


def main(path):
    cases=[{'variables':[],'clauses':[]},{'variables':[0],'clauses':[[]]},
           {'variables':[0],'clauses':[[1]]},{'variables':[0],'clauses':[[-1]]},
           {'variables':[0],'clauses':[[1],[-1]]},{'variables':[0,1],'clauses':[[1,-1,2]]},
           {'variables':[0,1],'clauses':[[1,2],[-1,-2]]},
           {'variables':[0,1],'clauses':[[1],[2],[-1,-2]]}]
    total=0
    for s in cases:
        source=any(all(any(a[abs(x)-1]==(x>0) for x in c) for c in s['clauses']) for a in itertools.product([False,True],repeat=len(s['variables'])))
        out=subprocess.run(['python3',str(path)],input=json.dumps(s),text=True,capture_output=True,check=True)
        t=json.loads(out.stdout);w,queries=target(t)
        assert source==(w is not None)
        calls=0;witnesses=[]
        if w is not None:
            witnesses.append(w)
            root=value({'poly':[-2,0,1],'root':2})
            algebraic={'W':[[encode(value(row[0])*root),row[1]] for row in w['W']], 'H':[[encode(value(x)/root) for x in w['H'][0]],w['H'][1]]}
            witnesses.append(algebraic)
            if len(t['X'])>3:
                # A nonoptimal witness, with exact slack-certified perturbation.
                X=[[Q(x) for x in row] for row in t['X']]
                Y=[[sum(Q(w['W'][i][k])*Q(w['H'][k][j]) for k in range(2)) for j in range(len(X))] for i in range(len(X))]
                slack=Q(t['tau'])-sum((X[i][j]-Y[i][j])**2 for i in range(len(X)) for j in range(len(X)))
                assert slack>0
                amount=min(Q(1),slack/(100*len(X)**2*(1+max(map(max,X)))**2))
                changed=json.loads(json.dumps(w));changed['W'][0][0]=str(Q(changed['W'][0][0])+amount)
                witnesses.append(changed)
            for witness in witnesses:
                valid(t,witness)
                ans=subprocess.run(['python3',str(path),'--extract'],input=json.dumps({'source':s,'target_solution':witness}),text=True,capture_output=True,check=True)
                a=json.loads(ans.stdout);assert len(a)==len(s['variables']) and all(type(x) is bool for x in a)
                assert all(any(a[abs(x)-1]==(x>0) for x in c) for c in s['clauses'])
                calls+=1
        total+=calls
        print(json.dumps({'source':s,'target':t,'yes':source,'cut_queries':queries,'witnesses':witnesses,'recovery_calls':calls}),flush=True)
    print(json.dumps({'sources':len(cases),'recovery_calls':total}),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--candidate',required=True,type=Path);a=p.parse_args();main(a.candidate)
