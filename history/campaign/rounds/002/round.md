# Round 2: stability for arbitrary threshold witnesses

## Plan

Prove a quantitative strengthening of round 1 for all nonnegative rank-two
products, without assuming symmetry, optimality or orthogonal supplied factors.
Scope: one column-space projection argument and one two-level rounding lemma;
no expanded numerical search. The goal is a polynomial modulus strong enough
for a rational graph perturbation. Use round 1's endpoint identity. The previous
sign-normalization experience is inapplicable: it does not preserve loss.
Reject this route if rank-two products close in objective can remain a fixed
distance from every two-block matrix while epsilon and excess vanish suitably.

## Evidence and diagnosis

Let X0=I+epsilon J, u=1/sqrt(n), 0<epsilon*n<=1. Suppose nonnegative Y has rank
at most two and ||X0-Y||_F^2<=n-2+eta, with eta<1 and
eta<2 epsilon*n+epsilon^2*n^2. Its rank must be exactly two. Let P be its column
space projector and theta=||(I-P)u||. Orthogonal projection gives the exact identity

    ||X0-Y||_F^2 = n-2 + (2 epsilon*n+epsilon^2*n^2)theta^2
                   + ||PX0-Y||_F^2.

Choose unit v in range(P) orthogonal to u. Q=uu^T+vv^T satisfies
||P-Q||_F=sqrt(2)*theta, so

    ||Y-(Q+epsilon J)||_F <= sqrt(eta)+2 sqrt(eta/(epsilon*n))
                          <= t := 3 sqrt(eta/(epsilon*n)).

For min(v)=-a,max(v)=b, nonnegativity of Y implies ab<=1/n+epsilon+t.
The round-1 endpoint identity then gives each coordinate's distance to its
nearest endpoint at most sqrt(n(epsilon+t)). Let w be the nearest-endpoint
vector. Both endpoint classes are nonempty. Center w to w0, then normalize to
v0; centering cannot increase ||w-v|| and

    ||v-v0|| <= 2||v-w0|| <= 2n sqrt(epsilon+t).

The span of 1 and w is exactly the two-block constant subspace, so
Q0=uu^T+v0 v0^T is its averaging projector. Therefore

    ||Y-(Q0+epsilon J)||_F <= D := t+4n sqrt(epsilon+t).

This is a general author proof, not a finite solver observation. No experiments,
source instances or recovery subprocess calls this round. A nonnegative
rank-one Y cannot satisfy eta<1, by the singular-value lower bound.

If D<1/(2n), the associated partition is recovered without an eigensolver:
put j with vertex 1 exactly when Y[1,j]>epsilon+1/(2n). Same-block entries
are epsilon+1/|S|; cross-block entries are epsilon. Thus every accepted factor
witness can eventually be decoded by constant-degree algebraic arithmetic and
comparisons once a threshold enforces this D bound. Coordinate encoding and
bit bounds remain obligations. No full reduction yet; no independent review.

Experience extraction: extend the pending round-1 projector entry with this
stability/recovery lemma; no duplicate new entry. No shared writes. Timing and
token usage unavailable. Prospects improve from unknown to promising but remain
uncalibrated because the discrete graph objective has not been connected yet.

## Next action

Perturb X0 by delta A, where A is nonnegative symmetric with constant row sum.
On two-block projectors, tr(PA) is two times that row sum minus a cut ratio.
Derive finite rational scales making rounding error smaller than the source's
rational decision gap. Audit both signs of the loss identity before composing.
