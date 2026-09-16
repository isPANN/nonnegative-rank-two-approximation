"""Independent exact checks; never imports the candidate or its checkers."""
import itertools
import json
import subprocess
import sys
from fractions import Fraction as F
from pathlib import Path

sys.set_int_max_str_digits(0)
ROOT = Path(__file__).resolve().parents[2]
ALGORITHM = ROOT / 'work/algorithm.py'

def call(payload, extract=False):
    return subprocess.run([sys.executable, str(ALGORITHM)] + (['--extract'] if extract else []), input=json.dumps(payload), text=True, capture_output=True)

def truth(clauses, x):
    return all(any(x[abs(l)-1] == (l>0) for l in c) for c in clauses)

def graph(s):
    v=len(s['variables'])+1+len(s['clauses']); B=[[0]*(2*v) for _ in range(2*v)]
    triples=[]
    for j,c in enumerate(s['clauses']):
        a,b,c=(c+[c[-1]]*2)[:3];z=len(s['variables'])+2+j
        triples += [(a,b,z),(-z,c,len(s['variables'])+1)]
    def add(a,b,k):
        if a!=b:B[a][b]+=k;B[b][a]+=k
    for i in range(v):add(2*i,2*i+1,2*len(triples)+1)
    for triple in triples:
        ids=[2*(abs(l)-1)+(l<0) for l in triple]
        for i,j in itertools.combinations(ids,2):add(i,j,1)
    return B,(2*len(triples)+1)*v+2*len(triples)

def witness(s):
    B,K=graph(s);h=len(B);n=2*h
    good=[]
    for rest in itertools.product([False,True],repeat=h-1):
        side=(False,)+rest
        cut=sum(B[i][j] for i in range(h) for j in range(i) if side[i]!=side[j])
        if cut>=K:good.append(side)
    assert bool(good)==any(truth(s['clauses'],x) for x in itertools.product([False,True], repeat=len(s['variables'])))
    out=json.loads(call(s).stdout);X=[[F(t) for t in row] for row in out['X']];tau=F(out['tau'])
    eps=min(X[i][j] for i in range(n) for j in range(n) if i!=j)
    result=None
    for half in good:
        side=half+tuple(not t for t in half);sizes=[side.count(False),side.count(True)]
        W=[[str(int(t==b)) for b in [False,True]] for t in side]
        H=[[str(eps+F(int(t==b),sizes[b])) for t in side] for b in [False,True]]
        loss=sum((X[i][j]-sum(F(W[i][r])*F(H[r][j]) for r in range(2)))**2 for i in range(n) for j in range(n))
        assert loss<=tau
        p=call({'source':s,'target_solution':{'W':W,'H':H}},True)
        assert p.returncode==0,p.stderr
        assert truth(s['clauses'],json.loads(p.stdout))
        result=(W,H,X,tau,eps)
    return len(good),result

def main():
    counts=[];base=None
    for clauses in [[[1]],[[-1]],[[1],[-1]],[[1,-1]],[[1,1,1]],[[1,-2],[2]]]:
        n=max(abs(l) for c in clauses for l in c)
        s={'variables':list(range(n)),'clauses':clauses}
        count,result=witness(s);counts.append({'clauses':clauses,'accepted_literal_cuts':count})
        if clauses==[[1]]:base=(s,result)
    print(json.dumps({'exact_composition_and_actual_witnesses':counts}))
    s,(W,H,X,tau,eps)=base
    # Exact asymmetric, nonoptimal perturbation whose loss is checked independently.
    slack=tau-sum((X[i][j]-sum(F(W[i][r])*F(H[r][j]) for r in range(2)))**2 for i in range(len(X)) for j in range(len(X)))
    bump=slack/(100*(1+sum(sum(row) for row in X)))
    H2=[row[:] for row in H];H2[0][0]=str(F(H2[0][0])+bump)
    loss=sum((X[i][j]-sum(F(W[i][r])*F(H2[r][j]) for r in range(2)))**2 for i in range(len(X)) for j in range(len(X)))
    assert loss<=tau
    original_loss=tau-slack
    H3=[row[:] for row in H];H3[0][0]=str(F(H3[0][0])+2*bump)
    twice_loss=sum((X[i][j]-sum(F(W[i][r])*F(H3[r][j]) for r in range(2)))**2 for i in range(len(X)) for j in range(len(X)))
    assert min(original_loss,twice_loss)<loss
    p=call({'source':s,'target_solution':{'W':W,'H':H2}},True)
    assert p.returncode==0 and truth(s['clauses'],json.loads(p.stdout))
    print(json.dumps({'asymmetric_nonoptimal_witness':'passed'}))
    # Same valid product, with a finite permitted coordinate scaling.
    huge=10**5000
    Wlarge=[[str(F(t)*huge) for t in row] for row in W]
    Hlarge=[[str(F(t)/huge) for t in row] for row in H]
    assert all(sum(F(Wlarge[i][r])*F(Hlarge[r][j]) for r in range(2))==sum(F(W[i][r])*F(H[r][j]) for r in range(2)) for i in range(len(X)) for j in range(len(X)))
    payload={'source':s,'target_solution':{'W':Wlarge,'H':Hlarge}}
    (Path(__file__).parent/'large-valid-witness.json').write_text(json.dumps(payload))
    p=call(payload,True)
    print(json.dumps({'large_valid_witness_returncode':p.returncode,'stderr':p.stderr}))
    # Reducible and repeated-root encodings for zero and one; contract permits both.
    algW=[[{'poly':[0,0,-1,1],'root':2 if F(t)==1 else 1} for t in row] for row in W]
    p=call({'source':s,'target_solution':{'W':algW,'H':H}},True)
    assert p.returncode==0 and truth(s['clauses'],json.loads(p.stdout)),p.stderr
    print(json.dumps({'repeated_reducible_algebraic_roots':'passed'}))

if __name__=='__main__':main()
