# Nonnegative rank-two approximation

This repository records a proposed deterministic Karp reduction from 3-SAT to
nonnegative rank-two squared-Frobenius approximation. It contains the complete
mathematical argument, forward construction and witness recovery, finite tests,
a Lean proof of the complete mathematical reduction and witness recovery, and the
retained exploration history.

For a nonnegative rational matrix X and a nonnegative rational threshold tau,
the target asks whether nonnegative real factors W and H, with inner dimension
at most two, satisfy

$$\|X-WH\|_F^2 \le \tau.$$

The factors have no orthogonality or symmetry constraints. The input rank is
unrestricted. The finite witness contract uses real-algebraic coordinates encoded
by dense integer polynomials and distinct-real-root indices. Recovery must work
for every valid encoded witness of a constructed target, including nonoptimal
witnesses; its runtime is measured in source plus witness bit length.

## Read and review

1. Read the [paper](paper/manuscript.pdf), with [Typst source](paper/manuscript.typ).
   It gives the construction, both implications, recovery, and bit bounds.
2. Inspect the [input and witness contract](algorithm/contract.md) and
   [algorithm](algorithm/algorithm.py). The [literature audit](paper/literature.md)
   states the novelty claim and the limits of its search.
3. Inspect the [formal statement and verification instructions](formal/README.md).
4. Trace the reasoning through the [exploration index](history/README.md),
   including abandoned approaches, counterexamples, reviews and repairs.

The intended contribution is quantitative rounding of arbitrary nonnegative
near-optimal rank-two products, composed with a gap-preserving cut construction.
The standard NAE and matching gadgets are not claimed as original. Human expert
correctness, priority and significance assessment remain outstanding.

## Verification status

| Scope | Evidence and limit |
|---|---|
| Mathematical reduction and witness recovery | Complete written argument; native agent review advanced after a parser repair. No independent human certification. |
| Stability lemma | Complete `NMF.stability : NMF.StabilityClaim`; local Lean build, transitive axiom audit and fresh Lean kernel replay passed. |
| Independent formal checking | Comparator and an independently implemented kernel have not run; deferred at the owner's request. |
| Reduction correctness | `NMF.Reduction.correctness` proves output legality, YES/NO equivalence and recovery from every valid real factor pair, including exceptional source branches. Local build, axiom audit and fresh kernel replay passed. [Unified entry and scope](formal/README.md). |
| Polynomial bounds and Python agreement | Not formalized. Complexity is outside the current requested scope. |
| Executable checks | Finite tests include YES/NO inputs and algebraic, nonoptimal and large-coordinate witnesses. Nontrivial NMF verdicts use proof-assisted cut certificates, not unrestricted global NMF solves. |

The Lean result proves mathematical correctness under Lean's foundations.
Polynomial resource bounds and agreement with Python/Z3 remain outside that proof. See the
[original verification report](history/campaign/work/verification.md) for test
coverage and shared mathematical dependencies. Fresh export checks are recorded
in [evidence](evidence/README.md).

## Run the algorithm and finite checks

Use Python 3.12 and [uv](https://docs.astral.sh/uv/), then run from this directory:

```sh
uv sync --locked
uv run --locked python algorithm/check.py --self-test
uv run --locked python algorithm/check.py --candidate algorithm/algorithm.py
uv run --locked python algorithm/verify.py --candidate algorithm/algorithm.py
uv run --locked python algorithm/check-repair.py
```

uv creates and manages the local `.venv`; no manual activation is needed.
`pyproject.toml` declares the direct dependencies, `uv.lock` pins their complete
dependency graph, and `.python-version` selects Python 3.12.
`algorithm.py` reads a source JSON instance from standard input and writes the
target JSON. With `--extract`, it reads an object containing `source` and
`target_solution` and writes a Boolean assignment. See the contract for the
precise accepted encodings. Z3 supplies exact algebraic arithmetic in recovery;
the construction and recovery do not call its decision solver.

With Typst installed, rebuild the paper using:

```sh
typst compile paper/manuscript.typ paper/manuscript.pdf
```

## Check the Lean proof

Install elan, then run from the repository root:

```sh
cd formal
lake exe cache get
lake build
lake env leanchecker --fresh Reduction
```

The unified entry is [Reduction.lean](formal/Reduction.lean). Its theorem
`NMF.Reduction.correctness` proves output legality, satisfiability equivalence and
recovery from every valid real factor pair. The final axiom audit contains only
`propext`, `Classical.choice` and `Quot.sound`. See the
[proof map](formal/README.md#proof-map) and
[complete verification evidence](formal/evidence/entry/README.md) for details.

No Codex session, research runner, sibling repository or local Docker is required.
Standard Python and Lean dependencies are installed separately; dependency caches
are not committed.

## Archive policy

This is a private, owner-maintained research archive. Issues, pull requests,
discussions, projects, wiki and Actions are disabled. Corrections and new evidence
are committed directly, preserving Git history.

Git history begins with this archive import; it does not reconstruct earlier
commits. The initial commit preserves the available source records as an import snapshot.
`history/` retains exploration records; formalization attempts are grouped under
`history/formalization/`, while the final Lean project appears only in `formal/`.
Current reviewable artifacts live in `paper/`, `algorithm/` and `formal/`.
Do not edit the snapshot to retroactively change what an earlier attempt claimed.
No public release or open-source license is implied by this private archive.
