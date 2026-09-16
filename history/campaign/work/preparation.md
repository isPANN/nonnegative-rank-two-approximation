# Preparation evidence

The independent source oracle uses Z3 SAT; six stored cases agree with direct
Boolean enumeration. The target oracle uses Z3 5.1.0 QF_NRA on nonnegative
products and their 3-by-3 minors, then solves exact factors. Its equivalence uses
the rank-two nonnegative-rank equality recalled in Section 1 of
https://arxiv.org/html/2507.20612v1. Candidate code is never imported.

`python3 work/check.py --self-test` passed three hand-checkable target cases:
a zero scalar, a full-rank 2-by-2 nonnegative matrix, and (I_3,0), which is NO
by rank. Algebraic sqrt(2) factors are accepted exactly; their wrong-loss and
negative-factor variants are rejected. Evidence: [self-test](evidence/preparation/self-test.jsonl).
`python3 work/evidence/preparation/harness-check.py` rejects malformed output,
a wrong decision, and wrong recovery: [log](evidence/preparation/harness.jsonl).
The harness checks both a returned witness and its component-permutation symmetry.
No complete candidate or candidate recovery call is claimed.

The first direct-factor oracle had produced the two positive checks but no
answer to (I_3,0) when the simpler equivalent minor formulation was completed.
Its unfinished query was cancelled after superseding that encoding, not declared
UNSAT. The [old program](evidence/preparation/factor-oracle-before.py) and
[partial log](evidence/preparation/factor-oracle-partial.jsonl) are preserved.
No execution-time cutoff is installed. The final formulation completed all cases.
Unknown and failures are errors, not NO. No numerical local optimizer is an oracle.

The tests cover at most three rows/columns and three source variables. Harder
positive-error instances can be much more expensive. Exact algebraic witnesses
avoid assuming rational optima, but their polynomial-size existence and efficient
recovery on a constructed family remain proof obligations, not preparation claims.

## Round-4 target and representation refinements

The full construction supplies matrices beyond practical generic QF_NRA checks.
The final candidate harness uses the explicitly documented
[proof-assisted certificate](verification.md) for nontrivial outputs, with exact
cut decisions and conservative real-objective bounds. Unsupported matrix forms
or unresolved boundary bands fail explicitly. This does not silently replace
real feasibility by a rational or canonical-witness restriction. Its NO answers
depend on the general stability lemma, so independent mathematical review is
required and is not replaced by passing program checks.

The generic QF_NRA checker remains available and supplies the tiny-instance
self-test. The dense algebraic-coordinate representation now bounds degree by
encoding length; earlier unrestricted SMT-LIB root text was insufficient for
that bit-complexity claim. This is an interface repair, not a change from real
to rational feasibility. Dense polynomial and root-index checks are tested with
sqrt(2). Current logs are round 4's self-test-certified.jsonl and harness-final.jsonl.
