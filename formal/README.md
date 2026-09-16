# Formal verification

The unified entry is [Reduction.lean](Reduction.lean). It proves
`NMF.Reduction.correctness : NMF.Reduction.Correctness` and audits that theorem's
transitive axiom dependencies. The default `lake build` target is `Reduction`.
A missing proof of the complete claim therefore fails the default build.

[ReductionSpec.lean](ReductionSpec.lean) defines the typed source language, rational
target instances, concrete forward construction, real-factor feasibility, witness
recovery and the complete correctness claim. [Challenge.lean](Challenge.lean)
states the same claim separately for Comparator. Its `sorry` is a specification
placeholder; the solution never imports it.

## Complete claim

For every typed source instance, `Correctness` proves all three obligations:

1. `forward s` is a nonempty nonnegative rational matrix with a nonnegative
   rational threshold.
2. The source is satisfiable if and only if `forward s` has nonnegative real
   factors of inner dimension two within that threshold.
3. For every such factor pair, `recover s W H` satisfies the original source.

The source allows clauses of zero through three literals and an empty conjunction.
The proof includes both exceptional branches. Target witnesses need not be optimal,
symmetric, normalized or rational. Recovery uses the first product row and the
same threshold and relative Boolean comparison as the mathematical algorithm.

The forward map is defined using exact rational arithmetic. Recovery is a
noncomputable Lean function over real comparisons; this models its mathematical
meaning, not an implementation of a real-algebraic comparison engine.

## Proof map

| File | Contribution |
|---|---|
| [Reduction.lean](Reduction.lean) | Complete theorem, including the exceptional branches. |
| [SourceGraphProof.lean](SourceGraphProof.lean) | Literal indexing, SAT/graph correspondence, threshold bounds, composition and recovery. |
| [MatchingProof.lean](MatchingProof.lean) | Matching and complement adjacency matrices, cut counts, both cut implications and threshold legality. |
| [ReductionProof.lean](ReductionProof.lean) | Diagonal regularization, bounds derived from integer matrices, and correctness of the rational cut-to-NMF construction. |
| [GraphReduction.lean](GraphReduction.lean), [BooleanReduction.lean](BooleanReduction.lean) | Clause padding, Boolean gadgets, explicit weighted graph and assignment recovery. |
| [CutMatrix.lean](CutMatrix.lean), [Perturbation.lean](Perturbation.lean) | Exact losses, nonnegative factors, integer cut gaps and perturbation bounds. |
| [Recovery.lean](Recovery.lean), [Stability.lean](Stability.lean) | Arbitrary-witness stability and recovery of block membership from entries. |
| [Definitions.lean](Definitions.lean) | Explicit Frobenius-square and stability definitions. |

## Reproduce local verification

Install elan, then run from this directory:

```sh
lake exe cache get
lake build
lake env leanchecker --fresh Reduction
```

Lean 4.32.2 and Mathlib v4.32.2 are pinned by the Lake project. The complete theorem's
axiom audit reports only `propext`, `Classical.choice` and `Quot.sound`, with no
`sorryAx` or custom mathematical axioms. Build, replay and implementation comparison
evidence is recorded in [evidence/entry](evidence/entry/README.md).

The replay uses Lean's own kernel. [comparator.json](comparator.json) now selects
`Challenge`, `Reduction` and `NMF.Reduction.correctness`. Comparator matching and
nanoda verification remain deferred at the owner's request; neither was run here.
The trusted boundary includes `ReductionSpec` and its imports, which must also be
reviewed for correspondence to the intended problem.

## Scope not certified

The theorem establishes mathematical correctness of the Lean construction and
recovery function. It does not prove polynomial runtime or encoding size, which
are outside the current request. It also does not verify JSON parsing, Python
execution or Z3's algebraic-number decoder and comparisons. Differential checks
are finite implementation evidence, not a proof of implementation agreement.
Novelty and significance remain separate research judgments.

Earlier component-only verification is retained in [evidence/reduction](evidence/reduction/README.md)
and [evidence/stability](evidence/stability/). Those records describe the scope
at the time they were produced; the complete theorem above is the current entry.
