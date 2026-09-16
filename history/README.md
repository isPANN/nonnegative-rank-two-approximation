# Exploration history

Imported on 2026-09-16 from the retained
`reduction-research/campaigns/nonnegative-rank-two-approximation` campaign.
The initial Git commit preserves all 134 retained campaign files byte-for-byte, excluding
`.lake` dependency/build caches, Python bytecode, virtual environments and OS
metadata. Git commit dates start with the import. The current tree keeps one formal project
at `formal/` in the repository root. Earlier formalization attempts live in
`history/formalization/`; identical copies of the final Lean project and its final
logs were removed from `campaign/`. No unique historical file was discarded.

## Reading order

| Stage | Record |
|---|---|
| Screening and rejected signed-offset/anchor routes | [Screening audit](research/evidence/nonnegative-rank-two-approximation-screening.md) and [exact checker](research/evidence/nonnegative-bordered-offset-probe.py) |
| Fixed problem | [Question](campaign/question.md) |
| Test foundation | [Preparation](campaign/work/preparation.md), [fixtures and early failures](campaign/work/evidence/preparation/) |
| Round 1: near-identity geometry | [Plan, evidence and reflection](campaign/rounds/001/round.md) |
| Round 2: arbitrary-witness stability | [Plan, proof and reflection](campaign/rounds/002/round.md) |
| Round 3: cut perturbation | [Plan, exact checks and reflection](campaign/rounds/003/round.md) |
| Round 4: full composition and recovery | [Plan, checks, failures and closure](campaign/rounds/004/round.md) |
| Native agent review and repairs | [Review](campaign/reviews/complete-rule/review.md), [follow-up](campaign/reviews/complete-rule/review-followup.md), [manuscript review](campaign/reviews/complete-rule/manuscript-review.md) |
| Formalization attempts and failures | [Raw logs and intermediate sources](formalization/endpoint/) |
| Completed local stability proof | [Final evidence](../formal/evidence/stability/) and [state](campaign/state.md) |

Four discovery rounds were completed from a budget of twenty. Formalization and
packaging are not additional discovery rounds. Round records contain experience
extraction and pending shared-entry proposals. The related retained experience
records are [exact-border obstruction](research/experience/exact-nonnegative-borders-allow-signed-residuals.md)
and [sign-factor gauge](research/experience/positive-narrow-sign-factor-gauge.md).
The latter was considered inapplicable to this approximation loss.

## Provenance and limitations

Historical records retain their original claims, status labels, local paths and
commands. Read them chronologically: a screening hold or an early successful
check does not describe the final result. Old commands using `work/` or `rounds/`
assume the working directory is `history/campaign/`.

The copied `campaign/work/screening.md` originally used links relative to the
research evidence directory. Its linked local checker and obstruction experience
are retained under `history/research/`; use the screening-audit link above.
References to other research campaigns or entries that were only proposed remain
historical references, not promised files in this repository. The sign-factor
gauge entry cites another campaign that is not part of this archive.

Raw Codex conversation transcripts and complete intermediate source snapshots
were not retained among the campaign files. Missing or previously deleted
material is not reconstructed. This repository claims completeness for the
retained files, not for every interaction or transient edit made during discovery.
Original dependency packages and build caches can be fetched through the pinned
Lake and Python dependency files rather than stored as exploration evidence.

The live paper, algorithm and Lean sources were copied from the initial snapshot.
Only packaging changes were applied: the paper's audit link now points into this
archive, and the live large-coordinate regression locates its adjacent algorithm.
The mathematical manuscript and proof sources were not changed.
