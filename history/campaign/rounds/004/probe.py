import itertools,json,sys
from pathlib import Path
from fractions import Fraction as F
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'work'))
from algorithm import sat_graph,complement
literals=[1,-1,2,-2]
clauses=[list(c) for k in [1,2,3] for c in itertools.combinations(literals,k)]
formula_count=0;accepted=0;cuts=0
for k in range(3):
 for cs in itertools.combinations(clauses,k):
  s={'variables':[0,1],'clauses':list(cs)}
  B,K=sat_graph(s);n=len(B);found=False
  for mask in range(1<<(n-1)):
   side=[bool(mask>>i&1) for i in range(n)]
   score=sum(B[i][j] for i in range(n) for j in range(i) if side[i]!=side[j]);cuts+=1
   if score>=K:
    a=[side[2*i]!=side[4] for i in range(2)]
    assert all(any(a[abs(x)-1]==(x>0) for x in c) for c in cs)
    found=True;accepted+=1
  expected=any(all(any(a[abs(x)-1]==(x>0) for x in c) for c in cs) for a in itertools.product([False,True],repeat=2))
  assert found==expected;formula_count+=1
print(json.dumps({'formulas':formula_count,'maxcut_partitions':cuts,'accepted_witnesses':accepted,'NAE_composition':'pass'}),flush=True)
graphs=[];edges=list(itertools.combinations(range(4),2))
for mask in range(64):
 B=[[0]*4 for _ in range(4)]
 for z,(i,j) in enumerate(edges):B[i][j]=B[j][i]=(mask>>z)&1
 graphs.append(B)
for weights in [(1,2,3),(2,5,1),(7,1,9)]:
 B=[[0]*4 for _ in range(4)]
 for i,w in enumerate(weights):B[i][i+1]=B[i+1][i]=w
 graphs.append(B)
queries=0;partitions=0;accepted=0
for B in graphs:
 E=sum(map(sum,B))//2
 for K in range(E+1):
  C,k=complement(B,K);h=len(B);n=len(C);found=False
  for mask in range(1,1<<(n-1)):
   S={i for i in range(n) if mask>>i&1};T=set(range(n))-S
   ratio=F(sum(C[i][j] for i in S for j in T),len(S)*len(T));partitions+=1
   if ratio<=k:
    assert len(S)==h and all((i in S)!=(h+i in S) for i in range(h))
    assert sum(B[i][j] for i in range(h) for j in range(i) if (i in S)!=(j in S))>=K
    accepted+=1;found=True
  expected=any(sum(B[i][j] for i in range(h) for j in range(i) if ((mask>>i)^(mask>>j))&1)>=K for mask in range(1<<h))
  assert found==expected;queries+=1
print(json.dumps({'matching_graphs':len(graphs),'threshold_queries':queries,'all_partitions':partitions,'accepted_cuts':accepted,'matching_complement':'pass'}))
