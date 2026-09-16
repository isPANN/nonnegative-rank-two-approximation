# Independent complete-rule review

Date: 2026-09-16. Decision: **revise**, for one executable arbitrary-witness failure. The general reduction argument survives this audit; no mathematical soundness gap was found. Novelty and significance are supported at the scope stated below. This decision is not an approval for publication or a substitute for human expert review.

Reviewed: README, AGENTS, research-review skill, fixed question, current contract, algorithm, proof, preparation, verification, and rounds 2–4. No candidate/checker implementation was imported, no author files were edited, and no additional agents were used. The proof uses the campaign's own projector argument; the round records explicitly reject transferring the unrelated sign-normalization experience. No external experience entry supplies a premise in this proof.

## Required correction

**R1: recovery rejects a valid finite rational witness.** `work/algorithm.py:63` calls `F(t)`, and line 77 applies it to the first factor row. Python's default decimal integer conversion limit rejects a 5,001-digit numerator. The contract places no such coordinate-size ceiling and explicitly requires recovery polynomial in source plus supplied witness length. `work/proof.md:155–171` therefore describes an abstract recovery algorithm that the executable does not implement for every permitted witness.

The independent `checks.py` constructs a valid canonical witness for `{"variables":[0],"clauses":[[1]]}`, verifies its exact loss against the actual forward output, and rescales **all** of W by 10^5000 and **all** of H by 10^-5000. Every entry remains nonnegative rational, the dimensions are unchanged, and an exact Fraction calculation verifies every product entry is unchanged. Nevertheless `--extract` exits 1 with `ValueError: Exceeds the limit (4300 digits)`. See `large-valid-witness.json` and `results.jsonl`.

Required repair: remove the runtime decimal-digit ceiling before input decoding and rational conversion, without imposing a new mathematical witness restriction. The same issue can affect JSON integer polynomial coefficients, so configuring only Fraction is insufficient. Run the saved witness in a fresh process and verify the recovered assignment; retain a runnable regression assertion. This is a local implementation repair, not a new research round or a reason to redesign the reduction. Reuse the unaffected proof and literature audit.

## Correctness audit

### Discrete composition

The two NAE clauses have the asserted existential equivalence after orienting f=false. This holds with repeated literals and repeated padding. All variable values, including auxiliary values, may be complemented together. A literal triangle contributes either 0 or 2 even with repetitions; discarded loops contribute zero. The cut weight decomposes into at most Pv from variable edges plus at most 2t from triangles, so meeting Pv+2t forces every desired condition. P=2t+1 is more than sufficient.

For the matching construction, an a-vertex smaller side cuts at most a matching edges. Its density is at most M/b+E/(ab). With b>=h+1 the deficit below M/h is at least M/[h(h+1)]=E+1, strictly larger than the possible E/(ab) bonus. A balanced cut missing a matching edge falls below Mh because M>E. Thus the complement threshold forces exactly the intended balanced, mate-separated cuts, and every accepted cut recovers SAT. For these source graphs K<=E: each NAE triangle has at least two distinct literal vertices because its fresh auxiliary variable differs from the other variables; its total nonloop weight is at least two. Consequently k is nonnegative with the enormous chosen M. No negative target threshold or omitted source case is needed.

### Arbitrary-product stability

I derived the projection identity independently. Put z=epsilon*n and gamma=2z+z^2. Since X0^2=I+gamma*uu^T, an arbitrary rank-two column projector P gives

    ||(I-P)X0||_F^2 = n-2+gamma*||(I-P)u||^2.

The decomposition into this residual and PX0-Y is orthogonal regardless of symmetry of Y. Rank one is excluded by eta<1. The plane range(P) intersects u-perp in a unit direction v; eta<gamma excludes theta=1. The two planes share v, giving ||P-Q||_F=sqrt(2)*theta. As gamma>=2epsilon*n and ||X0||_2<=2, the error is at most sqrt(eta)+2sqrt(eta/(epsilon*n)), hence the stated t when epsilon*n<=1.

For the two extrema of v, the entrywise error bound and Y>=0 yield alpha*beta<=1/n+epsilon+t. Expanding the endpoint sum gives exactly n*alpha*beta-1. Each summand is the product of the two endpoint distances and dominates the square of the smaller distance. In fact summing directly gives the stronger ||v-w||<=sqrt(n(epsilon+t)); the author's n*sqrt(epsilon+t) is conservative. The rounded vector is nonconstant, so centering and normalization are legitimate, and ||v-v0||<=2||v-centered(w)|| follows from the reverse triangle inequality. Finally ||vv^T-v0v0^T||_F<=2||v-v0||. No optimum, symmetry, normalized factor, or orthogonality premise has been inserted.

### Constants, loss, and rounding

Writing a=delta*L, the triangle bound gives excess at most (2+2n)*a+2a^2<=4n*a for n>=3 and a<=1. The chosen delta makes t=epsilon/2 exactly. The definitions also imply epsilon<=r/4 and r<1/(2n), so D<=epsilon+r/2<=3r/4<r. Both eta<1 and eta<gamma hold by very large margins. The trace identity uses constant row sums and the same undirected cut convention throughout.

Expanding around X0, the universal base loss n-2 leaves the cross term 2delta*<X0-Y,A>. Replacing Y by P_S+epsilon J changes it by at most 2delta*L*r. Therefore the lower bound in proof Section 4 has the correct sign and covers nonoptimal products. A rejected rational cut lies at least 1/(q*n^2) above k. The remaining margin is delta*(n*g-2Lr)>0. For first-row recovery the cross-block entries are below epsilon+1/(2n), while same-block entries exceed that threshold because 1/|S|>=1/n. This proves the arbitrary-witness implication over real coordinates.

### Encoding and algorithm

The forward construction uses O(s) vertices, O(s^2) rational entries, and fixed powers of polynomially bounded integers; the stated O(s^2 log(s+2)) output bit bound is supported. The existential YES witness is rational with small bit size. For arbitrary supplied algebraic witnesses, each comparison combines only four coordinates. Dense degree bounds and a constant number of algebraic operations permit polynomial resultant degrees, coefficient heights, isolation and sign testing; there is no need to build a field containing every matrix coordinate. This supports the abstract polynomial recovery claim. It does not remove the concrete runtime parsing failure R1.

`checks.py` additionally exercised reducible, repeated-root dense polynomial encodings for 0 and 1, which this Z3 installation interprets consistently with distinct-real-root indexing. Those checks passed. Malformed witnesses need not be recovered; the failure R1 uses a fully valid one.

## Independent executable evidence and its limits

Command: `python3 campaigns/nonnegative-rank-two-approximation/reviews/complete-rule/checks.py`.

The script exhausts literal cuts for six separately specified formulas, including a contradictory pair, a tautology, repeated literals and a two-variable formula. It finds seven accepted canonical cuts, builds factors independently, checks exact loss against actual forward outputs, invokes recovery in fresh subprocesses and checks SAT assignments directly. All seven recoveries pass. A separately verified asymmetric, nonoptimal product passes recovery. Repeated/reducible algebraic encodings pass. The large valid rational witness fails as described above.

These are direct feasible-witness and composition checks, not unrestricted real target solves. In particular the contradictory source has no accepted enumerated canonical cut; its unrestricted NMF NO conclusion rests on the audited general proof. I did not repeat the author's cut-certificate suites or claim their agreement independently establishes the stability lemma. No generic unrestricted solver was launched here. The proof, rather than numerical solver evidence, supports the universal claim.

## Novelty audit

Search date: 2026-09-16. Searches included rank-two/nonnegative/Frobenius complexity, projector/sparsest-cut connections, orthogonal NMF, symmetric NMF and the new EPMF result. The following primary works were checked at the indicated locations.

- [Lindy, Noferini and Van Dooren, 2507.20612v1](https://arxiv.org/html/2507.20612v1), Section 1, explicitly leaves rank-two approximate NMF hardness open. The arXiv record still lists v1 only. Lemma 2.3 and Theorem 2.4 supply related extremal-coordinate geometry; they should be credited when presenting the quantitative endpoint argument. They do not supply this Karp reduction or its perturbation soundness theorem.
- [Gillis and Glineur, 0810.4225](https://arxiv.org/pdf/0810.4225), Section 3.1, equation (3.1), Theorem 4, Corollary 1 and Theorem 5: NF uses a signed input with forbidden positions replaced by -d. Remark 1 explicitly discusses why a hard signed residual suggests difficulty for NMF. That observation is not a hardness transfer to nonnegative input or fixed rank two.
- [Gillis, Saha, Sicilia and Vandaele, 2607.04875v1](https://arxiv.org/html/2607.04875v1), Definition 4.1 and Theorem 4.2; also [v2](https://arxiv.org/html/2607.04875v2), Section 4, Theorem 4.1. The current revision changes the numbering, but still studies arbitrary real factors followed by entrywise absolute power. Its YES witness has rows (1,u_i), and when u_i=-1 the product has negative entries in an anchor block before absolute value. Thus even p=1 does not provide a rank-two nonnegative product. Hardness for this different feasible set does not imply the candidate theorem. This comparison checks the actual hypotheses and YES construction, not merely titles.
- [Asteris, Papailiopoulos and Dimakis, 2015](https://papers.nips.cc/paper/2015/file/eae27d77ca20db309e056e3d2dcd7d69-Paper.pdf), equation (1), Section 1 and Theorem 2: orthonormality of one factor is part of ONMF, and their approximation guarantee is additive. It neither removes that constraint nor supplies an exact polynomial threshold solver at the vanishing precision used here. The candidate proves closeness to a block structure without imposing ONMF constraints.
- [Kuang, Ding and Park, 2012](https://faculty.cc.gatech.edu/~hpark/papers/DaDingParkSDM12.pdf), Sections 1–2: symmetric NMF ties the factors and serves graph clustering. A hardness assertion for tied factors would not by itself establish soundness for the unrestricted factors allowed here.
- [Kubjas, Sodomaco and Tsigaridas, 2022](https://www.sciencedirect.com/science/article/am/pii/S0024379522000362), Section 6 and Example 6.2: algebraic critical-point enumeration for nonnegative rank-two approximation is relevant equivalent-formulation literature. It does not give a polynomial-time global solver for growing dimensions or this hardness theorem.

Judgment: the reviewed primary results do not subsume the complete unrestricted rank-two reduction, and the 2025 explicit open problem supports its novelty. The spectral projection estimates and endpoint variance identity are elementary/related to known geometry; novelty should be claimed for the quantitative synthesis and gap-preserving reduction, not for all their constituent inequalities. This is a bounded literature audit, not a proof of universal priority: unpublished work, inaccessible papers and unindexed later results remain unresolved coverage. No matching reduction was located in the inspected sources.

## Significance and disposition

The mathematical result meets the fixed significance target: exact threshold hardness for standard unweighted Frobenius approximation with nonnegative real factors and inner dimension two. Strictly positive symmetric constructed matrices are allowed properties of outputs, while every asymmetric feasible product remains covered. The result has polynomial output size, explicit rational YES witnesses and deterministic source recovery; it does not claim NP membership for the entire algebraic target language, constant-factor inapproximability, or practical optimization difficulty at ordinary numerical precision.

Repair R1 and return the unchanged mathematics with focused fresh-process recovery evidence. No new construction or full review restart is called for. After that repair, this audit supports advancement toward expert review, subject to the workflow's manuscript and inspection requirements.
