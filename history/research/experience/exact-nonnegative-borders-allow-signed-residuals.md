# Exact nonnegative borders allow signed rank-one residuals

Tags: nonnegative factorization, Schur complement, offset component, anchor, soundness.

## Claim and applicability

For the scalar-anchor matrix family in the cited audit, exact matching of the
anchor and constant border by nonnegative rank-two factors does not force a
nonnegative rank-one Schur residual. A signed residual can be represented by
mixing both nonnegative components. Scaling the anchor or increasing penalties
on its already-zero residual entries does not eliminate this witness.

## Evidence and status

The [bordered-anchor audit](../evidence/nonnegative-rank-two-approximation-screening.md#exact-bordered-anchor-obstruction-2026-09-16)
gives explicit rational factors for every positive rational scale s. Their
squared error is 9 for a threshold-32 target whose intended signed rank-one
source has optimum 33. The border is exact and the Schur residual has negative
off-diagonal entries. A Fraction checker verifies four scales. Evidence type:
symbolic counterexample family with finite arithmetic corroboration. Recorded
2026-09-16; no independent review, no new complexity theorem. Origin: screening.

## Consequence for search

Before amplifying a border, test exact-border solutions for the intended sign
restriction. Rank reduction through a Schur complement does not provide that
restriction. Repairing this family needs additional structural constraints or
a different construction, not stronger weights on the same border entries.
The claim does not exclude other nonnegative-rank-two reductions.

## Use history

No subsequent applications recorded.
