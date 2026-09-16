# Focused follow-up review

Date: 2026-09-16. Decision: **advance** toward expert review, subject to the remaining manuscript and visual-inspection workflow. This is an independent agent review, not human validation or publication acceptance.

The sole blocking finding R1 from `review.md` is repaired. `work/algorithm.py:6` now sets `sys.set_int_max_str_digits(0)` before either JSON input decoding or algebraic/rational conversion. This directly removes the accidental coordinate-size ceiling without weakening the mathematical witness contract.

I independently ran the original review checks in fresh candidate subprocesses; `results-followup.jsonl` records passing composition/witness cases, asymmetric strictly nonoptimal recovery, reducible/repeated-root encoding recovery, and successful extraction from the formerly failing large rational witness.

The new `check-repair.py` adds explicit regression assertions. It reads the saved valid 10^5000-rescaled witness and requires a successful exit and satisfying source assignment. It then replaces every integer W coordinate c by the dense polynomial `[-c,1]` with root index 1. These represent exactly the same coordinates, so the product and previously established feasibility remain unchanged; the JSON now contains 5,001-digit integer polynomial coefficients. Both fresh-process recoveries return `[true]`. Evidence is `repair-results.jsonl`.

Commands:

```
python3 campaigns/nonnegative-rank-two-approximation/reviews/complete-rule/checks.py
python3 campaigns/nonnegative-rank-two-approximation/reviews/complete-rule/check-repair.py
```

Correctness: the executable defect is closed. The unchanged general proof audit, including arbitrary asymmetric/nonoptimal products, constants, both source directions, recovery, and theoretical bit bounds, remains supported as recorded in `review.md`.

Novelty: the previous bounded primary-literature audit remains applicable, including the hypothesis comparison with EPMF v2 Theorem 4.1. Its explicit coverage limitations remain; this follow-up does not claim new or exhaustive literature coverage.

Significance: the theorem continues to meet the fixed standard unweighted rank-two Frobenius NMF target. The repair changes neither the problem nor the claimed contribution. No additional blocking finding remains from this review.
