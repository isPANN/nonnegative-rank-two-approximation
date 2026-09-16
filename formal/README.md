# Stability proof

[Stability.lean](Stability.lean) proves `NMF.stability : NMF.StabilityClaim`.
[Definitions.lean](Definitions.lean) contains the fixed statement and explicit
Frobenius-square, base-matrix and block-matrix definitions.
[Challenge.lean](Challenge.lean) separately states the same target for Comparator.
Its `sorry` is a specification placeholder; the solution does not import it.

The theorem covers arbitrary nonnegative real square matrices Y of rank at most
two. For n >= 3, epsilon > 0, epsilon*n <= 1 and
0 < eta < min(1, 2*epsilon*n + epsilon^2*n^2), it turns base loss at most n-2+eta
into proximity to a nonempty proper two-block partition. The bound is
`t + 4*n*sqrt(epsilon+t)`, where `t = 3*sqrt(eta/(epsilon*n))`.
Symmetry of Y, optimality, a supplied projector and prior block proximity are
not hypotheses.

## Proof map

| Obligation | Declaration |
|---|---|
| Column-space projection and trace | `exists_column_projection` |
| Exact error decomposition | `projection_error_identity` |
| Exclusion of rank at most one | `rank_two_of_near_optimal` |
| Quantitative plane comparison | `near_optimal_plane` |
| Endpoint rounding from nonnegativity | `nonnegative_endpoint_rounding` |
| Centering and normalization | `center_error`, `normalize_error` |
| Identification with the partition matrix | `two_level_projector`, `plane_rounding` |
| Full statement | `stability` |

## Reproduce local checking

Install [elan](https://github.com/leanprover/elan), then run from `formal/`:

```sh
lake exe cache get
lake build
lake env leanchecker --fresh Stability
```

The standard Lake files select Lean 4.32.2 and Mathlib v4.32.2. The solution's
`#print axioms NMF.stability` reports only `propext`, `Classical.choice` and
`Quot.sound`; it does not depend on `sorryAx` or additional mathematical axioms.
The installed toolchain calls the replay executable `leanchecker`. Replay uses
Lean's own kernel, not a separately implemented kernel.

The [original final build](evidence/stability/build.log) and fresh replay were
successful. The [replay log](evidence/stability/kernel-replay.log) is empty because
the checker returned exit code 0 without diagnostics; its recorded outcome is in
[the campaign state](../history/campaign/state.md#local-verification).
The standalone export also has a [local build log](../evidence/lean-build.log).

[comparator.json](comparator.json) selects the complete stability theorem and the
standard axiom allowlist, with nanoda configured as the external checker.
Comparator statement matching and independent kernel checking remain deferred
at the owner's request. No Docker or external checker was run during export.
The complete reduction, bit complexity and agreement with Python remain outside
this certificate's scope.
