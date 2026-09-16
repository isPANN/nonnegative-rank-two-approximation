import json
import sys
from fractions import Fraction as F
import z3

sys.set_int_max_str_digits(0)


def source(s):
    assert type(s) is dict and type(s['variables']) is list and type(s['clauses']) is list
    n=len(s['variables'])
    assert all(type(x) is int for x in s['variables']) and s['variables']==list(range(n))
    assert all(type(c) is list and len(c)<=3 and all(type(x) is int and 1<=abs(x)<=n for x in c) for c in s['clauses'])
    return n


def sat_graph(s):
    n=source(s); m=len(s['clauses']);nv=n+1+m; false=n+1
    clauses=[]
    for j,c in enumerate(s['clauses']):
        a,b,c=(c+[c[-1]]*3)[:3];z=n+2+j
        clauses.extend([(a,b,z),(-z,c,false)])
    B=[[0]*(2*nv) for _ in range(2*nv)]
    def edge(i,j,w):
        if i!=j:B[i][j]+=w;B[j][i]+=w
    heavy=2*len(clauses)+1
    for i in range(nv):edge(2*i,2*i+1,heavy)
    for clause in clauses:
        v=[2*(abs(x)-1)+int(x<0) for x in clause]
        for i,j in [(0,1),(1,2),(2,0)]:edge(v[i],v[j],1)
    return B,heavy*nv+2*len(clauses)


def complement(B,K):
    h=len(B);E=sum(map(sum,B))//2;M=h*(h+1)*(E+1);cap=M
    W=[[0]*(2*h) for _ in range(2*h)]
    for i in range(h):
        for j in range(h):W[i][j]=B[i][j]
        W[i][h+i]=W[h+i][i]=M
    C=[[cap-W[i][j] if i!=j else 0 for j in range(2*h)] for i in range(2*h)]
    return C,F(cap)-F(M,h)-F(K,h*h)


def cut_map(C,K):
    n=len(C);d=max(map(sum,C))
    A=[[C[i][j]+(d-sum(C[i]) if i==j else 0) for j in range(n)] for i in range(n)]
    L=1+n+sum(map(sum,A))+2*d+n*(max(map(max,C))+1)
    gap=F(1,K.denominator*n*n);radius=gap/(16*L*n)
    epsilon=radius**2/(256*n*n);delta=epsilon**3/(144*L)
    norm=sum(x*x for row in A for x in row)
    tau=n-2+2*delta*(sum(A[i][i] for i in range(n))-2*d+n*(K+gap/2))+delta**2*norm
    X=[[F(int(i==j))+epsilon+delta*A[i][j] for j in range(n)] for i in range(n)]
    return {'X':[[str(x) for x in row] for row in X],'tau':str(tau)},epsilon


def forward(s):
    source(s)
    if not s['clauses']:return {'X':[[0]],'tau':0}
    if any(not c for c in s['clauses']):return {'X':[[1,0,0],[0,1,0],[0,0,1]],'tau':0}
    B,K=sat_graph(s);C,k=complement(B,K)
    return cut_map(C,k)[0]


def number(t):
    if isinstance(t,str):return z3.RealVal(str(F(t)))
    assert type(t) is dict and type(t['poly']) is list and t['poly'] and t['poly'][-1]!=0
    assert all(type(c) is int for c in t['poly']) and type(t['root']) is int and t['root']>0
    terms=' '.join(f'(* {c if c>=0 else "(- "+str(-c)+")"} (^ x {i}))' for i,c in enumerate(t['poly']))
    text=f'(root-obj (+ {terms}) {t["root"]})'
    a=z3.Real('value')
    expr=z3.parse_smt2_string('(assert (= value '+text+'))',decls={'value':a})
    return z3.simplify(expr[0].arg(1))


def extract(s,w):
    n=source(s)
    if not s['clauses']:return [False]*n
    B,K=sat_graph(s);C,k=complement(B,K);_,epsilon=cut_map(C,k)
    first=[number(v) for v in w['W'][0]]
    side=[]
    threshold=z3.RealVal(str(epsilon+F(1,2*len(C))))
    for j in range(len(C)):
        y=z3.simplify(first[0]*number(w['H'][0][j])+first[1]*number(w['H'][1][j]))
        side.append(z3.is_true(z3.simplify(y>threshold)))
    return [side[2*i]!=side[2*n] for i in range(n)]


if __name__=='__main__':
    if '--extract' in sys.argv:
        s=json.load(sys.stdin)
        print(json.dumps(extract(s['source'],s['target_solution'])))
    else:
        try:out=forward(json.load(sys.stdin))
        except (AssertionError,KeyError,TypeError,ValueError):out={'X':[[1,0,0],[0,1,0],[0,0,1]],'tau':0}
        print(json.dumps(out))
