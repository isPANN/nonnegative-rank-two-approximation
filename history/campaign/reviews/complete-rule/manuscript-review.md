# Manuscript consistency check

Date: 2026-09-16. Scope: `work/manuscript.typ` source only; the main researcher owns PDF rendering and visual inspection. The existing mathematical advance decision stands. One local wording correction is needed before delivery.

## Required wording correction

In **From 3-SAT to a weighted cut threshold / Literal graph**, immediately after the display `K=p_0 v+2t`, the manuscript says K “is the maximum possible cut weight.” For an unsatisfiable source, no cut reaches K, so its actual maximum cut weight is smaller. Replace that phrase with **“is an upper bound on every cut weight.”** The immediately following equivalence about cuts reaching K is correct and should remain. This is a transcription/wording error, not a gap in the reviewed reduction.

## Checked and consistent

- Theorem 1 states a deterministic Karp reduction to nonnegative real rank-at-most-two products with rational input and threshold. The witness-size qualifier measures recovery in source plus supplied witness length, and the text does not claim polynomial witnesses for arbitrary target instances.
- The NAE composition, heavy matching, complement threshold, C-to-A regularization, gap and scale definitions, and target threshold match the audited rule. The manuscript includes the needed K<=E explanation.
- Lemma 3 has the needed epsilon and eta premises. Projection, plane distance, endpoint sum, centering/normalization and projector-distance estimates are transcribed correctly. It does not require a symmetric or optimal product.
- The base-excess estimate, t=epsilon/2, rounding radius, signed loss bound, rational cut gap and first-row strict threshold all match the proof. Zero components and exceptional source cases remain covered.
- Encoding bounds and constant-arity algebraic comparisons match the reviewed argument. The small output bit length and arbitrary supplied coordinate bit length are distinguished.
- The primary citations use the appropriate models and locations. In particular EPMF cites v2 Theorem 4.1, whereas its v1 theorem number was 4.2. The absolute-value/sign distinction and acknowledgment of prior endpoint geometry are accurate.
- The scope section avoids NP-membership and constant-factor hardness claims. The reproducibility appendix explicitly identifies the large-output target verdicts as conditional cut certificates; it does not describe them as unrestricted NMF solves. The independent-check counts and repaired large-coordinate tests agree with the review evidence.
- Figure captions mark the endpoint picture as conceptual and the block epsilon as illustrative. They do not present those scales as actual constructed-instance parameters.

No other theorem, equation, quantifier, caveat or reference discrepancy was found in this source check. After the local correction above, this manuscript is consistent with the reviewed rule. This check does not certify the rendered layout or establish human peer review.
