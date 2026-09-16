# Positive narrow coordinates for sign-realization factors

Tags: sign-rank, normalization, factorization, projective-chart, reciprocal-guard

## Claim and applicability

Given any zero-free rank-at-most-r real sign realization and eta>0, column
sign flips determined by its first sign row permit a factorization UV with
|U_ih|<=1 and 1<=V_hj<=1+eta. Undoing those known flips recovers the original
signs. For rational supplied factors and rational eta, the normalization uses
polynomially many rational operations with polynomial output bit length.
It does not find a realization from its sign matrix or preserve an arbitrary
matrix-approximation witness's loss.

## Evidence and status

[Round 13](../../campaigns/entrywise-l1-low-rank/rounds/013/round.md) gives
the basis change, positive column scaling, affine coordinate compression and
positive row scaling. The [probe](../../campaigns/entrywise-l1-low-rank/rounds/013/probe.py)
checks two rational rank-two examples, including coordinates from -100 to 100.
Evidence type: general elementary normalization, main-researcher proof, no
independent review or novelty claim.

## Consequence for search

Reciprocal guard products V_hl/V_hj can lie in a fixed interval near one on
the completeness side. Soundness still needs a proof that EVERY accepted
target witness obeys suitable bounds, or can be repaired without crossing
the threshold. A convenient normalized YES witness does not give that premise.

## Use history

Extracted at Round 13 closure on 2026-09-15.

[Round 14](../../campaigns/entrywise-l1-low-rank/rounds/014/round.md) used
the existence of bounded positive factors to test a reciprocal-guard array.
The coarse interval [1,2] still allowed cross-entry savings to dominate its
copy penalties. This failure motivates using the lemma's adjustable width;
it does not invalidate the normalization itself.

[Round 15](../../campaigns/entrywise-l1-low-rank/rounds/015/round.md) used
eta<=1/n to prove that own-pair penalties dominate all guard cross savings.
The 256 finite checks support the displayed all-real inequality; the
normalization still applies only to an existing source realization.
