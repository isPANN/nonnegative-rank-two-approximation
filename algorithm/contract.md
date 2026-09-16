# Exact input and witness contract

Source JSON: `{"variables":[0,...,n-1],"clauses":[[signed one-based literals],...]}`.
Clauses have at most three literals. Witness: a length-n JSON Boolean list.
Each clause must have a true literal. Empty conjunctions/clauses are allowed.

Target JSON: `{"X":[[rational entries]],"tau":rational}`. Rational values are
integers or Fraction-compatible strings, represented in binary in the complexity
model and decimal text for interchange. X is a nonempty rectangular nonnegative
matrix and tau is nonnegative. Witness JSON has `W` (m by 2) and `H` (2 by n).
Each value is a rational string or `{"poly":[a0,...,ad],"root":k}`,
with a dense list of integer coefficients and the one-based index among distinct
real roots. The last coefficient is nonzero. Degree is bounded by the explicit
list length; sparse exponent encodings are not permitted. These values are
converted to Z3 root-obj constants for exact arithmetic only.
Equivalent exact algebraic values are valid. Finite algebraic witnesses exist
for nonempty semialgebraic sets over Q; this does not imply polynomial witness
bit size. A completed construction must separately prove its encoding and
recovery bounds. The question is real feasibility, not rational-only feasibility.

`algorithm.py` maps one source JSON from stdin to target JSON on stdout.
`algorithm.py --extract` receives `source` and `target_solution` and returns an
assignment. Fresh processes, no retained metadata, no solver in either map.
The extractor must work for every accepted encoded algebraic witness of its
output; it cannot demand optimality. Its runtime is measured in source plus
witness bit length. Malformed sources may map to (I_3,0), a fixed NO.

The target oracle first solves nonnegative rank-at-most-two product Y with all
3-by-3 minors zero and squared Frobenius error <=tau, then obtains W,H by an
exact feasibility query. For nonnegative matrices, ordinary rank at most two
equals nonnegative rank at most two. Thus this is equivalent to the original
language; it is not a relaxation. Independent witness validation multiplies
W,H and compares exact algebraic values, without invoking the decision solver.
