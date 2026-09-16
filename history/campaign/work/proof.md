# Candidate reduction proof

Status: author proof; independent review required. Fixed source: 3-SAT. Target:
nonnegative real rank-two squared-Frobenius approximation of a nonnegative
rational matrix. No symmetry, orthogonality or additional constraints on factors.

## 1. Weighted graph composition

Pad nonempty clauses to length three by repeating the last literal. Introduce
one variable f and one z_j per clause (a,b,c), replacing it by NAE(a,b,z_j) and
NAE(not z_j,c,f). With f=false, these two clauses are satisfiable exactly when
(a or b or c) is true. For if a=b, z_j is forced opposite a and the second clause
excludes precisely c=f=a. If a!=b, choose z_j to satisfy the second clause.
Complementing every Boolean value preserves NAE, so any NAE witness may be
oriented to f=false and yields a satisfying original assignment.

Let v be the number of original and auxiliary variables and t the number of
NAE clauses. Build a weighted undirected graph B with two vertices for each
positive/negative literal. Give each variable pair an edge of weight P=2t+1.
Each NAE clause contributes its triangle of unit edges. Repeated endpoints
create loops, which contribute zero and are discarded; parallel edges add.
Every triangle contributes either zero or two to any cut, including repeated
literals. Therefore a cut of weight at least K=Pv+2t cuts every variable pair
and makes every clause nonmonochromatic. Conversely each NAE assignment attains
K. Restricting any such cut and orienting relative to f recovers the SAT witness.
These are standard Boolean/cut devices, not the claimed new numerical mechanism.

Write h=|V(B)|, E=sum of undirected edge weights. Add one mate for every vertex
and edges (i,i') of weight M=h(h+1)(E+1). Retain B on the original h vertices;
let W be this weighted graph on n=2h vertices. A balanced cut separating all
mates has density cut_W/(ab)=M/h+cut_B/h^2, where a=b=h.

Every unbalanced cut with a<h<b has density at most M/b+E/(ab), which is strictly
less than M/h: the difference in the matching term is at least M/[h(h+1)]=E+1,
whereas E/(ab)<=E. A balanced cut missing any mate edge has weight at most
M(h-1)+E<Mh. Thus any cut with density at least M/h (and in particular at least
M/h+K/h^2) is balanced and separates all mates. Its original restriction has
weight at least K exactly when this latter density threshold holds.

Complement W with capacity M: C_ij=M-W_ij for i!=j, C_ii=0. M exceeds every
original weight. Its cut density is M-cut_W/(ab). Hence the original 3-SAT
instance is YES exactly when C admits a nontrivial cut of density at most
k=M-M/h-K/h^2. All accepted such cuts recover SAT witnesses as described.
Here 0<=k<=max(C)=M and n>=3 for all nontrivial constructed sources. The matching
complement entries are zero, which also helps recognize the test family.

## 2. Matrix construction

For the integer nonnegative symmetric C, let d=max_i sum_j C_ij and
A=C+diag(d-sum_j C_ij). Thus A is entrywise nonnegative, symmetric, has row sum d,
and its off-diagonal entries encode the cut weights. Let q be the denominator
of k in lowest terms and set

    g=1/(q n^2),
    L=1+n+sum_ij A_ij+2d+n(max_ij C_ij+1),
    r=g/(16Ln), epsilon=r^2/(256n^2), delta=epsilon^3/(144L).

Output X=I+epsilon J+delta A and threshold

    tau=n-2+2delta[tr(A)-2d+n(k+g/2)]+delta^2||A||_F^2.

The simple exceptional cases are an empty conjunction, mapped to ([0],0), and
an empty clause or malformed source, mapped to (I_3,0). The first always has
witness zero and recovers any assignment. The second is NO by rank.

All nontrivial output entries are strictly positive rationals. Since n>=3,
delta L is much smaller than 1/2 and the bracket magnitude is <=L, tau>0.
Also epsilon*n<=1, delta L<=1, ||A||_F<=L and
|tr(A)-2d+n(k+g/2)|<=L, directly from the definitions and 0<=k<=max(C).

For any nontrivial partition S,T of sizes a,b, let P_S be the orthogonal
projector averaging within each block. It is nonnegative of rank two and
P_S*1=1. Y_S=P_S+epsilon J has nonnegative rank-two factors: row i of W is
(1,0) or (0,1) according to its block; H's corresponding row has value
1/a+epsilon on S and epsilon on T, or epsilon on S and 1/b+epsilon on T.

    tr(P_S A)=2d-n cut_C(S)/(ab),
    ||X-Y_S||_F^2=n-2+2delta[tr(A)-2d+n cut_C(S)/(ab)]
                         +delta^2||A||_F^2.

Thus each accepted source cut yields a target witness below tau. Notice that
these rational factors do not require square roots.

## 3. Arbitrary-witness stability

Let X0=I+epsilon J and u=1/sqrt(n). Its squared singular values are
(1+n epsilon)^2,1,...,1. For every rank-at-most-two Y, the unconstrained
approximation lower bound is ||X0-Y||_F^2>=n-2.

Suppose Y is any nonnegative product of two components satisfying
||X0-Y||_F^2<=n-2+eta, where eta<1 and eta<2epsilon*n+epsilon^2*n^2.
Rank one is impossible, since its residual lower bound is n-1. If P projects
onto the two-dimensional column space of Y and theta=||(I-P)u||, then

    ||X0-Y||_F^2=n-2+(2epsilon*n+epsilon^2*n^2)theta^2+||PX0-Y||_F^2.

Pick unit v in range(P) perpendicular to u, and Q=uu^T+vv^T. The two planes
share v and differ in the remaining direction by sine theta, so
||P-Q||_F=sqrt(2)*theta. Since ||X0||_2<=2,

    ||Y-(Q+epsilon J)||_F <= 3 sqrt(eta/(epsilon*n))=:t.

Write min v=-alpha, max v=beta. Both are positive in magnitude. Nonnegativity
of Y, evaluated at these two indices, implies alpha*beta<=1/n+epsilon+t.
Using sum v_i=0 and sum v_i^2=1 yields

    sum_i (v_i+alpha)(beta-v_i)=n alpha beta-1<=n(epsilon+t).

Each nonnegative summand bounds the square of the distance to the closer
endpoint. Round every coordinate to its nearest endpoint to obtain w, with
||v-w||_2<=n sqrt(epsilon+t). Both classes are nonempty because the two extrema
round to themselves. Center w and normalize; the resulting v0 satisfies
||v-v0||_2<=2n sqrt(epsilon+t). The span of 1 and w is the two-block constant
subspace, so uu^T+v0 v0^T=P_S for that partition. Consequently

    ||Y-(P_S+epsilon J)||_F <= t+4n sqrt(epsilon+t)=:D.

This argument does not assume Y symmetric or its supplied factors normalized.

## 4. Soundness at the chosen threshold

Let ||X-Y||_F^2<=tau for any valid target product. Since tau<=n+1 and
||A||_F<=L, triangle inequality gives

    ||X0-Y||_F^2 <= n-2+4n delta L.

Indeed, expand (sqrt(tau)+delta L)^2 and use sqrt(n+1)<=n and delta L<=1.
Take eta=4n delta L. The stated smallness conditions hold. Then
 t=3sqrt(eta/(epsilon*n))=6sqrt(delta L/epsilon)=epsilon/2<=epsilon,
and

    D<=epsilon+8n sqrt(epsilon)=epsilon+r/2<=3r/4<r<1/(2n).

Hence some nontrivial partition S satisfies the preceding distance bound.
For any such partition, expanding the loss and using Cauchy-Schwarz gives

    ||X-Y||_F^2 >= n-2+2delta[tr(A)-2d+n cut_C(S)/(ab)]
                         +delta^2||A||_F^2-2delta Lr.

If cut_C(S)/(ab)>k, its integer numerator and denominator ab<=n^2 imply
cut_C(S)/(ab)>=k+g. The right side would exceed tau by at least
 delta*n*g-2delta*L*r>0, a contradiction. Thus every accepted target witness
rounds to a source YES cut and then to a satisfying assignment. This establishes
the NO direction without asserting that an optimum is exactly a block matrix.

## 5. Executable recovery and complexity

Reconstruct epsilon and n deterministically. For each j, compute only the
first product-row entry Y_1j=W_10 H_0j+W_11 H_1j, and put j in the first block
if Y_1j>epsilon+1/(2n). Since D<1/(2n), this comparison exactly distinguishes
the block containing vertex 1 from the other block. Recover the original literal
cut from its first h entries. For original variable i, output true exactly when
its positive literal and f's positive literal are in different blocks.

The extractor needs no eigendecomposition, source search or decision solver.
Z3 is used only for exact algebraic constants and arithmetic comparisons. Each
comparison involves at most four supplied algebraic numbers and a rational.
Dense polynomial-plus-root-index encoding bounds each degree by its input
length. A constant number of algebraic operations and sign comparisons therefore
has polynomial bit complexity by standard univariate real-algebraic arithmetic;
no single field extension for all coordinates is built. Merely accepting sparse
exponent expressions would not justify this bound, so the contract uses dense
coefficient lists. The returned assignment has the explicitly listed source size.

For source encoding length s, v,h,n=O(s), E=O(s^2), M=O(s^4), d=O(s^5),
L=O(s^6), q=O(s^2). Every scalar has O(log(s+2)) bits with fixed constants;
negative powers only multiply these constant exponents. The target has O(s^2)
entries and O(s^2 log(s+2)) total bits. Fraction arithmetic and construction use
polynomial time (a conservative O(s^6) bit bound suffices). Recovery uses O(s)
constant-arity algebraic comparisons and deterministic reconstruction, polynomial
in source plus supplied witness length. YES outputs have polynomial-size rational
witnesses from the block factors. General target membership in NP is not claimed.

## 6. Novelty and validation limits

The proposed contribution is the quantitative nonnegative near-projector
stability and its gap-preserving graph perturbation for unrestricted rank-two
NMF. Standard NAE and cut compositions are credited as such. The primary open
question is Lindy, Noferini and Van Dooren, arXiv:2507.20612v1, Section 1.
Detailed novelty comparison, independent verification and native review remain
required. The candidate is not yet ready for expert review.
