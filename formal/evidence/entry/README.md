# Complete reduction verification

Date: 2026-09-16. Commands run from the standalone repository's `formal/` directory.
The fixed toolchain is Lean 4.32.2 with Mathlib v4.32.2.

## Complete theorem

`Reduction.lean` proves `NMF.Reduction.correctness : NMF.Reduction.Correctness`.
The claim covers output legality, source/target equivalence and recovery from
every valid real factor pair for every typed source, including both exceptional
branches. The default Lake target builds this proof, not merely the component
modules or the statement.

## Build and axiom audit

```sh
lake build
```

Outcome: passed. [complete-build.log](complete-build.log) contains the complete
theorem's transitive axiom audit: `propext`, `Classical.choice`, `Quot.sound` only.
There are no build warnings, errors, `sorryAx` dependencies or custom axioms in
the solution. Earlier logs retain failed elaboration attempts and repairs; those
failed outputs are not accepted proof evidence.

## Fresh kernel replay

```sh
lake env leanchecker --fresh Reduction
```

Outcome: passed, exit code 0. [kernel-replay.log](kernel-replay.log) is empty because
the checker completed without diagnostics. This replays the complete proof and
its dependencies using Lean's own kernel; it is not an independent kernel check.

## Trusted challenge

```sh
lake env lean Challenge.lean
```

Outcome: passed, exit code 0, with the expected specification-placeholder warning
in [challenge-elaboration.log](challenge-elaboration.log). The challenge is not
imported by the solution. Comparator is configured for the complete theorem but
has not run. Statement matching and nanoda checking remain deferred.

## Exact forward-map comparison

With the repository's Python environment installed, run:

```sh
lake env lean --run evidence/entry/ForwardCheck.lean > evidence/entry/forward-outputs.jsonl
uv run --locked --directory .. python formal/evidence/entry/CompareForward.py
```

Outcome: all six cases match the Python construction in every rational matrix
entry and in the threshold. The cases cover an empty conjunction, an empty clause,
a unit clause, contradictory units, a two-literal clause and a clause with repeated
literals. [forward-comparison.json](forward-comparison.json) records the sources
and results; [forward-outputs.jsonl](forward-outputs.jsonl) retains the Lean outputs.
These finite checks do not prove implementation agreement or verify the Z3 decoder.

## Limits

The complete theorem proves the mathematical Lean construction and real-valued
recovery semantics. Polynomial resource bounds, the Python/Z3 implementation,
novelty and independent formal checking are separate obligations. None is certified
by this result. No local Docker or remote verifier was used.
