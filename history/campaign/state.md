# Rank-two nonnegative approximation

Research status: **ready_for_expert_review** (agent review only).
Formal status: **complete local Lean proof of the stability lemma**; independent
verification deferred at the user's request. The complete reduction is not formally certified.
Twenty discovery rounds authorized; four completed,
sixteen unused. Stop reason: the fixed theorem has a complete rule and general
proof, passing applicable checks, independent review advance, and an inspected
English manuscript. Do not spend the remaining budget on duplicate attempts.

Result: a deterministic Karp reduction from 3-SAT to standard nonnegative
rank-two squared-Frobenius approximation, with polynomial output bit length and
polynomial recovery from every valid densely encoded algebraic target witness.
Nontrivial outputs are symmetric and strictly positive; factors remain unrestricted.
No NP-membership, constant-factor inapproximability, or practical-tolerance claim.

- [Fixed question](question.md)
- [Paper PDF](work/manuscript.pdf) and [native Typst source](work/manuscript.typ)
- [Forward and recovery algorithm](work/algorithm.py), [contract](work/contract.md)
- [Original general proof](work/proof.md), preserved with its pre-review status
- [Independent audit](reviews/complete-rule/review.md),
  [repair advance](reviews/complete-rule/review-followup.md), and
  [manuscript check](reviews/complete-rule/manuscript-review.md)
- [Verification and its limits](work/verification.md), [literature](work/literature.md)

Correctness: general proof independently audited; the sole executable blocker
was Python's decimal-digit parsing ceiling, repaired without restricting valid
witnesses. Fresh-process regressions pass for a 10^5000 rescaling and 5,001-digit
polynomial coefficients. No blocking review finding remains. This is internal
agent review, not human mathematical certification.

Novelty: inspected primary sources do not subsume the unrestricted rank-two
result; the 2025 paper explicitly lists its hardness as open. Related endpoint
geometry is credited. The July 2026 EPMF v2 result permits signed products followed
by absolute powers and does not directly transfer. Priority remains subject to
unindexed, inaccessible and unpublished work and human expert assessment.

Significance: the standard first nontrivial NMF approximation rank, rather than
an added graph-class or factor restriction. The reduction distinguishes exact
global threshold complexity from numerical heuristics. Expert review is the next
useful step; there is no calibrated publication or correctness probability.

| Round | Outcome |
|---|---|
| [1](rounds/001/round.md) | Near-identity optimum and endpoint rounding; 119 exact partitions |
| [2](rounds/002/round.md) | Quantitative arbitrary-product stability and first-row recovery |
| [3](rounds/003/round.md) | Weighted cut perturbation; 1,330 exact canonical checks |
| [4](rounds/004/round.md) | Full SAT composition, verification, parser repair, independent advance and manuscript |

The prepared suite covers six sources/six recoveries, and the separate author
verifier eight sources/fourteen recoveries; these overlap. Larger target NO
checks are exact cut certificates conditional on the stability lemma, not
unrestricted nonlinear solves. The reviewer directly audited that lemma.

Experience extraction: two proposed new entries and one existing-entry use update
are retained in round records; shared entries are pending under campaign-only
writes. Shared counts: zero new, zero updated, three pending. No board, skill,
production-library or external-repository modification; no publishing or
background jobs. The eight-page manuscript includes three checked vector figures,
complete proof, exact recovery, bit bounds and reproducibility limitations.

## Formalization pilot

Scope: the full arbitrary-witness stability lemma in Section 3 of
[the mathematical proof](work/proof.md). The solution is
`NMF.stability : NMF.StabilityClaim` in [Stability.lean](../../formal/Stability.lean).
The fixed [Definitions](../../formal/Definitions.lean) and separate
[Challenge](../../formal/Challenge.lean) retain the original target statement.
The solution does not import the challenge.

The theorem covers every nonnegative real square matrix Y of rank at most two
under the stated near-optimal Frobenius-error assumptions. It returns a nonempty
proper partition with the specified error bound. Symmetry of Y, a preselected
projector, an assumed rank-two column space, and prior closeness to a block matrix
are not input premises. The Frobenius square is the explicit double sum in the
trusted definitions. The proof connects it to Mathlib's Frobenius norm; vector
norms use EuclideanSpace, not the default sup norm on functions.

The complete proof chain is now implemented:

| Paper obligation | Lean declarations |
|---|---|
| Column-space projection, with trace equal to rank | `exists_column_projection` |
| Projection residual identity | `projection_error_split`, `projection_base_residual`, `projection_error_identity` |
| Exclusion of rank zero and one | `rank_two_of_near_optimal` |
| Orthonormal directions and quantitative plane comparison | `plane_projection_basis`, `matrix_projection_plane`, `matrix_projection_pythagoras`, `near_optimal_plane` |
| Nonnegativity and endpoint rounding | `nonnegative_endpoint_rounding`, `extrema_strict` |
| Centering, normalization, and block identification | `center_error`, `normalize_error`, `two_level_projector`, `plane_rounding` |
| Full stability statement with the original constants | `stability` |

The displacement of the normalized all-ones vector is linked to the explicit
squared row-sum expression by `unitOnes_image_sq`. The plane estimate retains
`3 * sqrt(eta / (epsilon * n))`; endpoint rounding, centering and normalization
retain the final `4 * n * sqrt(epsilon + t)` term. Both partition classes are
proved nonempty, and the vector being normalized is proved nonzero.

### Local verification

Lean 4.32.2 and Mathlib v4.32.2 are pinned through the standard Lake files.
`lake build` passes without warnings. The transitive axiom audit for the final
`NMF.stability` reports exactly `propext`, `Classical.choice`, `Quot.sound`.
It contains no `sorryAx`, custom mathematical axiom or native-computation axiom.
See [build.log](../../formal/evidence/stability/build.log).

Fresh Lean kernel replay of the completed theorem passed with exit code 0 and
no diagnostics. Its raw [kernel-replay.log](../../formal/evidence/stability/kernel-replay.log)
is therefore empty. This replay covers the full stability theorem and its imports.
The final challenge elaboration is recorded in
[challenge.log](../../formal/evidence/stability/challenge.log). The challenge now contains only the full stability target. Its explicit
specification placeholder is not accepted proof evidence.

Commands, all run from `campaigns/nonnegative-rank-two-approximation/formal`:

```sh
lake build
lake env lean Challenge.lean
lake env leanchecker --fresh Stability
```

The installed replay executable is named `leanchecker`. Its fresh replay uses the
Lean kernel; it is not an independently implemented checker.
[comparator.json](../../formal/comparator.json) now selects the complete `NMF.stability`
statement. Comparator statement matching in a separate clean environment and
external nanoda checking have not run. The current host is macOS; Comparator,
nanoda and landrun are not installed. The user explicitly deferred independent
verification on 2026-09-16. No host selection or remote setup is pending.
No local Docker installation or startup is authorized or performed.

### Scope limits and next action

| Verification scope | Status |
|---|---|
| Complete stability lemma | Lean build, transitive axiom audit and fresh kernel replay pass |
| Complete reduction, YES/NO equivalence and witness recovery | Not formalized |
| Polynomial runtime and encoding size | Not formalized |
| Agreement with the Python implementation | Not formalized; existing injected tests remain experimental evidence |

Clean statement comparison and independent kernel checking are deferred at the
user's request; resume them only when requested. This result does not certify
NP-hardness, novelty, practical significance, or the complete Karp reduction.
Human review still owns whether `StabilityClaim` expresses the intended lemma.

Development evidence remains in `formal/evidence/setup/` and
`formal/evidence/endpoint/`. Early broad imports and deleted generated cache files
caused resource pressure and dependency rebuilding; the cancelled jobs are not
proof evidence. Later failures were elaboration/API issues (matrix literals,
linear-map coercions, inverse-power orientation and complement cardinality) and
an overly broad arithmetic tactic reaching its default heartbeat limit. Focused
arithmetic premises repaired the latter without a wall-clock timeout or unbounded
search. Failed logs remain available; the successful final build supersedes them.
The full statement and manuscript were not weakened or rewritten, no campaign
algorithm changed, and no discovery round was charged.
