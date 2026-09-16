# Standalone export checks

These checks run against the exported live files, outside the research repository.
They validate packaging and executable behavior; they do not constitute independent
mathematical or external-kernel verification.

The original export checks used a fresh Python 3.12 environment installed with uv
from the requirements file retained in Git history. To reproduce the Python checks
with the current project, run `uv sync --locked` from the repository root and
prefix each Python command below with `uv run --locked`:

| Command | Output |
|---|---|
| `python algorithm/check.py --self-test` | [self-test.jsonl](self-test.jsonl) |
| `python algorithm/check.py --candidate algorithm/algorithm.py` | [prepared.jsonl](prepared.jsonl) |
| `python algorithm/verify.py --candidate algorithm/algorithm.py` | [verification.jsonl](verification.jsonl) |
| `python algorithm/check-repair.py` | [large-witness.jsonl](large-witness.jsonl) |
| `typst compile paper/manuscript.typ paper/manuscript.pdf` | [typst.log](typst.log) |
| `lake build` from `formal/` | [lean-build.log](lean-build.log) |

The Lean build reuses a local copy of the already installed dependency cache;
that cache is excluded from Git. Toolchain and dependency manifests are committed.
The retained original fresh kernel replay is documented in [formal/README.md](../formal/README.md).
Independent checking remains deferred.

All six commands above completed with exit code 0. The oracle self-test covers
six source cases, three target cases and algebraic/negative-witness regressions.
The prepared suite covers six sources and six recovery calls; the separate suite
covers eight sources and fourteen recovery calls. The suites overlap. Both
large-coordinate regressions pass. These counts are finite evidence, not a proof.

The paper rebuild has no diagnostics. All eight pages render pixel-identically
to the retained original PDF at a 1,000-pixel maximum dimension. The copied Lean
project builds and reports only the standard foundational axioms for
`NMF.stability`. The export did not repeat the already-passing kernel replay.

All 134 retained campaign files were compared byte-for-byte with their originals.
Live Lean sources and configuration, and the forward/recovery implementation and
principal test files, also match their retained originals. Live navigation links
resolve. Dependency caches, virtual environments and credentials are excluded
from Git; a secret-pattern scan of exported files passed.
