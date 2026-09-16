# Round 1: near-identity spectral anchors and two-block geometry

## Plan

Hypothesis: X0=I+epsilon J has a degenerate rank-two optimum whose nonnegative
representatives encode approximate bipartitions. This replaces the failed
signed-offset residual mechanism with an orthogonal-projector mechanism.
Scope: derive its exact global optimal family and an endpoint rounding inequality;
check every nontrivial bipartition on n=3..7 for epsilon=1/10000, with exact
rational matrix arithmetic. No graph perturbation or hardness claim this round.

Relevant experience: exact-nonnegative-borders-allow-signed-residuals excludes
repeating the scalar border; positive-narrow-sign-factor-gauge concerns sign
realizations and does not preserve this loss. Neither supplies a rounding lemma.
Completeness should encode a partition as P+epsilon J; soundness will eventually
need to round every low-loss Y, not just exact minimizers. First check whether
nonnegativity enforces two levels in the epsilon->0 family. Reject if an exact
minimizer stays a fixed distance from every bipartition as epsilon decreases.

## Evidence and diagnosis

`python3 rounds/001/probe.py` from the campaign directory checks 119 partitions
(n=3..7), with exact SymPy arithmetic; [output](result.json). P is the block
averaging projector, and Y=P+epsilon J has nonnegative factors using the two
block indicator columns and rows P's block rows plus epsilon. Its error against
I+epsilon J is exactly n-2.

General argument: X0 has singular values 1+n epsilon,1,...,1. Every best rank-two
approximation equals (1+n epsilon)uu^T+vv^T with u=1/sqrt(n), v orthogonal to u
and unit norm. This follows from the equality case of orthogonal projection,
not a nonnegative-factor normalization assumption. Set min(v)=-a,max(v)=b.
Nonnegativity gives ab<=1/n+epsilon; mean zero and squared norm one give
sum_i (v_i+a)(b-v_i)=nab-1>=0. Hence each coordinate is within sqrt(n epsilon)
of an endpoint. At epsilon=0, exactly two levels remain, corresponding to a
nontrivial bipartition. The explicit partitions attain the optimum.

This supports the new route but applies only to exact base minimizers. The
future graph perturbation and merely threshold-feasible witnesses need a
quantitative stability result. No Karp construction or source recovery exists yet.

Experience extraction: pending new `research/experience/nonnegative-projector-two-level-rounding.md`;
claim limited to rank-two near-identity minimizers and the endpoint identity.
Existing border-experience use update also pending; it helped avoid a ruled-out
mechanism, not prove this lemma. No shared writes under the campaign-only scope.
No independent review. Timing/token totals unavailable.

## Next action

Prove stability for every nonnegative rank-two Y with base loss at most n-2+eta.
Project its column space towards one containing the all-ones vector, then round
the remaining vector to two endpoint levels. If the bound is polynomial in n,
epsilon and eta, a second, smaller graph perturbation can encode a cut score.
