# Verification of the candidate

## Actual-output checking and its limitation

Both programs execute the actual forward algorithm and recover source witnesses
through fresh subprocesses; neither imports candidate code. Source decisions are
Z3 SAT in check.py and exhaustive Boolean enumeration in verify.py.

For nontrivial large outputs, the target decision check is a **proof-assisted
certificate**, not an independent unrestricted NMF solver. It recovers epsilon
from the smallest off-diagonal entry, a rational step delta from the gcd of
residual entries, and checks a symmetric nonnegative integer A with equal row
sums. It checks all inequalities needed by the projector stability bound from
the actual matrix and threshold, not from source metadata. It then queries cuts
within the bound's relaxed density threshold. For each cardinality the cut
weights are expressed through complementary weights; this is an exact identity.

If all cut queries are UNSAT/INFEASIBLE, the lemma certifies target NO. A found
cut yields explicit nonnegative factors and is accepted only after direct exact
loss validation. If a cut lands in the uncertainty band, the checker fails as
inconclusive; it never returns an unsupported decision. The source reduction's
rational gap is designed to avoid that band.

The prepared program uses Z3 pseudo-Boolean constraints; the separately authored
verifier uses OR-Tools CP-SAT with XOR variables as absolute differences. The
second program imports neither candidate nor prepared checker. They share the
mathematical stability lemma, which must be assessed independently. Agreement
between these programs does not independently validate that lemma or establish
real NMF hardness. The native reviewer must audit it directly.

The unrestricted small target oracle remains QF_NRA with nonnegative matrix
entries and all 3-by-3 minors zero, followed by exact nonnegative factor recovery.
Three hand-checkable tests pass. A direct QF_NRA candidate run returned the
empty-source case, but its 12-by-12 query was unfinished when the certificate
oracle superseded it and it was cancelled. No solver timeout or NO verdict was
assigned to that query. The partial log is retained in round 4.

## Commands and evidence

From the campaign directory:

```
python3 work/check.py --self-test
python3 work/check.py --candidate work/algorithm.py
python3 work/verify.py --candidate work/algorithm.py
python3 work/evidence/preparation/harness-check.py
```

[Round 4](../rounds/004/round.md) owns raw logs and final counts. Tests include
YES and NO formulas, empty clauses/conjunctions, repeated literals, component
permutations, exact irrational rescaling, and a strictly nonoptimal rational
factor perturbation that is directly checked against the actual threshold.

The first verifier invocation had a missing pathlib.Path import, raised NameError
before any test, and was repaired in place after retaining its source. This is
an execution repair, not mathematical evidence. The forward parser was also
repaired to map malformed JSON to the fixed target NO; both candidate suites
were rerun after that change. Independent review and focused repair review now advance the rule; see
[review](../reviews/complete-rule/review.md) and
[follow-up](../reviews/complete-rule/review-followup.md).

The reviewer exposed a valid-witness parser failure for 5,001-digit rational
coordinates. Removing Python's decimal conversion ceiling before JSON decoding
and Fraction conversion repairs both rational strings and integer polynomial
coefficients. The independent runnable regression and fresh-process results are
in `reviews/complete-rule/check-repair.py` and `repair-results.jsonl`.
The author reran the unchanged independent checks successfully in
`rounds/004/recovery-repair.jsonl`. This local parsing repair changes no
mathematics; the unaffected complete suites remain evidence.
