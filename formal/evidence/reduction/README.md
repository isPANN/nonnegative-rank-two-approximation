# Reduction component verification

Date: 2026-09-16. Working directory: `formal/` in the standalone private archive.
The pinned toolchain is Lean 4.32.2 with Mathlib v4.32.2.

## Local build and axiom audit

Command:

```sh
lake build
```

[build-final.log](build-final.log) records a successful build with no errors or
warnings. Every reported transitive axiom dependency is in the standard allowlist:
`propext`, `Classical.choice`, `Quot.sound`. None includes `sorryAx`. The five new
proof modules contain no `sorry`, `admit` or custom axiom declarations.
[default-target-build.log](default-target-build.log) checks the final Lake default:
`GraphReduction`, which imports all new proof modules and `Stability`.

The other build logs retain intermediate elaboration and tactic failures and their
repairs. Failed logs, including any inferred `sorryAx` dependency after an error,
are not accepted proof evidence. The final successful build supersedes them.

## Kernel replay

Command:

```sh
lake env leanchecker --fresh GraphReduction
```

Outcome: passed, exit code 0. The [kernel-replay.log](kernel-replay.log) is empty
because the checker completed without diagnostics.
This command uses Lean's own kernel. It is not Comparator matching or verification
by an independently implemented kernel.

## Scope

The checked statements and their assumptions are listed in
[the formal proof map](../../README.md#proof-map). They cover
individual general theorems, including arbitrary nonnegative real target factors,
not only finite test instances.

No full source-to-target theorem has been proved. Matching/complement adjacency,
regularization, parameter bounds for the exact rational output, exceptional-case
composition, and correspondence to the Python/Z3 implementation remain incomplete.
Complexity formalization is outside the current request. Comparator and independent
kernel verification remain deferred; no Docker or remote verifier was used.
