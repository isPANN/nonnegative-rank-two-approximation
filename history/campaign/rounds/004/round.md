# Round 4: complete 3-SAT composition and exact recovery

## Plan

Build one complete rule using rounds 1–3. Transform 3-SAT to NAE-3-SAT with a
shared false variable and one auxiliary per clause; encode NAE clauses as weighted
Max Cut triangles. Add heavy matching partners to force a balanced densest cut,
then complement weights to obtain the intermediate sparse-cut instance.

Finite scope: all 106 formulas of at most two clauses selected without repetition
from the fourteen distinct nonempty clauses of size at most three on two signed
variables; exhaustive Max Cut witnesses. Separately test the matching-complement
lemma on all 64 simple four-vertex graphs and three weighted four-vertex paths,
at every integer cut threshold from zero to total edge weight. These checks do
not yet globally solve NMF outputs. Complete forward and extraction modes, then
return to prepared target verification before any correctness claim.

The extractor should read the first product row, round a cut, restrict to the
original literal vertices and orient truth relative to the false variable.
Check arbitrary accepted cut witnesses, not only source-generated witnesses.
No prior experience supplies this particular composition; the round-3 cut lemma
is the active dependency. Matching and NAE mechanisms themselves are standard
techniques, not claimed as individually original.

## Evidence and diagnosis

The [complete implementation](../../work/algorithm.py) and
[general proof](../../work/proof.md) now cover original 3-SAT, every target
witness, all output restrictions and polynomial bit bounds. The complementary
capacity is M (the matching weight), preserving zero off-diagonal graph entries;
the earlier probe also checked capacity M+E+1. Both are equivalent density
complements; the retained final construction uses M. [Final discrete checks](results-final.jsonl):
106 formulas, 48,416 literal cuts and 442 accepted cut witnesses; 67 matching
graphs, 290 thresholds, 36,830 cuts and 1,428 accepted cuts. All reverse
implications were checked on every accepted enumerated cut.

The [prepared final suite](prepared-input-final.jsonl) passes six sources,
three YES/three NO, with six fresh-process recoveries and maximum matrix order
28. The [separate final suite](verification-input-final.jsonl) passes eight
sources, five YES/three NO, with fourteen recoveries and maximum order 24.
It includes exact sqrt(2) factor rescalings and strictly nonoptimal feasible
factor perturbations. Suites overlap. [Verification](../../work/verification.md)
explains that nontrivial target verdicts use exact cut certificates conditional
on the proved stability lemma; they are NOT independent unrestricted NMF solves.
Native review must specifically audit this shared mathematical dependency.

The direct QF_NRA candidate run remains [partial](prepared-nra-partial.jsonl):
it completed the trivial YES, not the subsequent 12-by-12 query. That query was
cancelled when replaced by the proof-assisted certificate checker. A dense
complementary-weight identity simplified the prepared cut constraints after
another partial run; no result was inferred from either unfinished computation.
No wall-clock timeout was installed. Smaller unrestricted algebraic self-tests
and deliberate faulty-fixture checks pass in [self-test-certified.jsonl](self-test-certified.jsonl)
and [harness-final.jsonl](harness-final.jsonl).

Repairs within this construction: dense coefficient-list algebraic coordinates
replace unrestricted root-expression syntax to justify degree/bit bounds;
the verifier's first execution failed on a missing Path import before any case;
and malformed forward JSON now maps to the fixed NO. Superseded files and logs
are retained here. Both candidate suites passed after the parser repair. These
are not new research mechanisms or rounds.

Experience extraction: the full composition supports the two pending projector
and cut-perturbation entries from rounds 1–3. Standard NAE and matching devices
are not extracted as original discoveries. The border-entry use-history update
remains pending. No shared writes; two proposed new entries, one update pending.
Timing/token totals unavailable. Four started rounds, three previously closed;
this fourth remains under independent review and potential writing.

## Next action

Independent native review of the exact theorem, stability constants, extractor
encoding complexity, proof-assisted testing limitation and novelty. Keep the
candidate and current proof unchanged during review. If substantive repair is
needed, revisit the responsible obligation rather than padding the budget.

## Closure

Completed after the [independent audit](../../reviews/complete-rule/review.md)
and [focused advance](../../reviews/complete-rule/review-followup.md).
The reviewer found a valid-witness failure for 5,001-digit rational coordinates:
Python's decimal parsing ceiling caused recovery to crash. Setting
`sys.set_int_max_str_digits(0)` before decoding and exact arithmetic repaired the
actual contract. The mathematical argument was unchanged. The independent
regression also covers 5,001-digit integer polynomial coefficients. The author
rerun is [recovery-repair.jsonl](recovery-repair.jsonl); independent repair evidence
is in the review directory. This local repair is part of round 4, not a new idea.

The [manuscript review](../../reviews/complete-rule/manuscript-review.md) requested
one wording repair: the literal threshold is an upper bound, not an attained
maximum for every source. It is corrected in the English native Typst manuscript.
PDF inspection also repaired attachment scope in cut/density notation and the
endpoint sum, fraction scope, title spacing and appendix numbering. The final
[paper](../../work/manuscript.pdf) has eight pages and three structural vector
figures; compilation has no diagnostics. All pages were visually inspected.
The technical-writing final pass retained the fixed quantifiers and caveats.

Final decision: ready_for_expert_review. Four research rounds completed of twenty
authorized, sixteen unused. Finite tests do not replace the general proof; human
expert mathematical and priority assessment remains outstanding. Two proposed
new experience entries and one prior-entry use update remain pending shared
synchronization under the campaign-only write boundary. No shared entries written.
