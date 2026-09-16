import itertools,json
from fractions import Fraction as F
from cut_map import map_cut
count=0;yes=0;maxbits=0
n=4;edges=list(itertools.combinations(range(n),2))
for graph in range(64):
 C=[[0]*n for _ in range(n)]
 for k,(i,j) in enumerate(edges):C[i][j]=C[j][i]=(graph>>k)&1
 for K in [F(0),F(1,3),F(2,3)]:
  if not graph and K:continue
  t,(A,e,z,g,L,r)=map_cut(C,K)
  assert z*L<=1 and n*e<=1 and e<=r/4
  eta=4*n*z*L
  assert eta<1 and eta<2*e*n+e*e*n*n
  assert 9*eta/(e*n)<=e*e and 2*L*r<n*g
  maxbits=max(maxbits,max(max(F(x).numerator.bit_length(),F(x).denominator.bit_length()) for row in t['X'] for x in row))
  for mask in range(1,2**(n-1)):
   S={i for i in range(n) if mask>>i&1};T=set(range(n))-S
   cut=sum(C[i][j] for i in S for j in T)
   ratio=F(cut,len(S)*len(T))
   Y=[[e+(F(1,len(S)) if i in S and j in S else F(1,len(T)) if i in T and j in T else 0) for j in range(n)] for i in range(n)]
   loss=sum((F(t['X'][i][j])-Y[i][j])**2 for i in range(n) for j in range(n))
   pred=n-2+2*z*(sum(A[i][i] for i in range(n))-2*max(map(sum,C))+n*ratio)+z*z*sum(x*x for row in A for x in row)
   assert loss==pred
   assert (loss<=F(t['tau']))==(ratio<=K)
   count+=1;yes+=ratio<=K
print(json.dumps({'graphs':64,'threshold_instances':190,'canonical_cut_checks':count,'accepted_canonical_witnesses':yes,'max_matrix_entry_bits':maxbits,'rational_loss_and_parameter_identities':'pass'}))
