"""Exact rational witnesses defeating one bordered offset anchor."""
from fractions import Fraction as F
import json

records = []
for s in [1, 2, 10, 10**6]:
    target = [[4*s*s, 4*s, 4*s], [4*s, 5, 0], [4*s, 0, 5]]
    w = [[F(s, 2), F(s, 2)], [F(1), F(0)], [F(0), F(1)]]
    h = [[F(4*s), F(13, 2), F(3, 2)],
         [F(4*s), F(3, 2), F(13, 2)]]
    y = [[sum(w[i][k]*h[k][j] for k in range(2)) for j in range(3)]
         for i in range(3)]
    assert all(v >= 0 for a in (w, h) for row in a for v in row)
    assert y[0] == target[0]
    assert all(y[i][0] == target[i][0] for i in range(3))
    error = sum((F(target[i][j])-y[i][j])**2 for i in range(3) for j in range(3))
    residual = [[y[i][j]-4 for j in range(1, 3)] for i in range(1, 3)]
    assert error == 9 < 32 < 33
    assert residual == [[F(5, 2), F(-5, 2)], [F(-5, 2), F(5, 2)]]
    assert residual[0][0]*residual[1][1] == residual[0][1]*residual[1][0]
    records.append(dict(anchor_scale=s, error=str(error),
                        w=[[str(x) for x in row] for row in w],
                        h=[[str(x) for x in row] for row in h],
                        residual=[[str(x) for x in row] for row in residual]))
print(json.dumps(records, indent=2))
