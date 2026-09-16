from fractions import Fraction as F


def map_cut(C,K):
    n=len(C);K=F(K)
    assert n>=3 and 0<=K<=max(map(max,C))
    assert all(type(C[i][j]) is int and C[i][j]>=0 and C[i][j]==C[j][i] for i in range(n) for j in range(n))
    assert all(C[i][i]==0 for i in range(n))
    d=max(map(sum,C))
    A=[[C[i][j]+(d-sum(C[i]) if i==j else 0) for j in range(n)] for i in range(n)]
    L=1+n+sum(map(sum,A))+2*d+n*(max(map(max,C))+1)
    gap=F(1,K.denominator*n*n)
    radius=gap/(16*L*n)
    epsilon=radius**2/(256*n*n)
    delta=epsilon**3/(144*L)
    norm=sum(x*x for row in A for x in row)
    tau=n-2+2*delta*(sum(A[i][i] for i in range(n))-2*d+n*(K+gap/2))+delta**2*norm
    X=[[F(int(i==j))+epsilon+delta*A[i][j] for j in range(n)] for i in range(n)]
    return {'X':[[str(x) for x in row] for row in X],'tau':str(tau)},(A,epsilon,delta,gap,L,radius)
