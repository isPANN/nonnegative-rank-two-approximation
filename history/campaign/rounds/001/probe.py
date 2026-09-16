import json
from fractions import Fraction as F
import sympy as s
count=0
for n in range(3,8):
 for mask in range(1,2**(n-1)):
  S=[i for i in range(n) if mask>>i&1];T=[i for i in range(n) if not mask>>i&1]
  P=s.Matrix(n,n,lambda i,j:s.Rational(1,len(S)) if i in S and j in S else s.Rational(1,len(T)) if i in T and j in T else 0)
  e=s.Rational(1,10000);Y=P+e*s.ones(n);X=s.eye(n)+e*s.ones(n)
  assert P*P==P and P*s.ones(n,1)==s.ones(n,1) and Y.rank()==2
  assert sum(z*z for z in X-Y)==n-2
  W=s.Matrix(n,2,lambda i,k:int((i in S)==(k==0)))
  H=s.Matrix(2,n,lambda k,j:(s.Rational(1,len(S)) if k==0 and j in S else s.Rational(1,len(T)) if k==1 and j in T else 0)+e)
  assert W*H==Y and min(W)>=0 and min(H)>=0
  count+=1
print(json.dumps({'partition_templates':count,'sizes':[3,4,5,6,7],'exact_loss_identity':'pass','nonnegative_factorizations':'pass'}))
