# Literature audit of the complete candidate

Search date: 2026-09-16. This is a bounded primary-source audit, not a certificate
of priority. Searches covered the exact rank-two Frobenius target, identity
perturbations/projectors, graph partition connections, and nearby factorization
hardness. No matching theorem was found in the inspected sources.

- Lindy, Noferini and Van Dooren, *On rank-2 Nonnegative Matrix Factorizations
  and their variants*, https://arxiv.org/html/2507.20612v1, Section 1 explicitly
  leaves hardness of rank-two approximation open. Sections 2–4 concern exact
  rank-two structure and suboptimal approximation/ANLS initialization, not a
  global polynomial decision algorithm. Exact rank-two feasibility is easy.
  The analogous fixed-rank statement is repeated in the authors' workshop
  abstract: https://events.dm.unipi.it/event/307/contributions/714/.
- Gillis and Glineur, *Nonnegative Factorization and the Maximum Edge Biclique
  Problem*, https://arxiv.org/pdf/0810.4225, Theorem 4, Corollary 1, Remark 1,
  and Theorem 5 (printed pp. 8–9): the hard NF data have negative entries -d.
  Remark 1 says that the signed residual subproblem suggests difficulty for
  fixed-rank NMF; it does not prove the nonnegative-input target. Increasing
  rank and adding an offset was already excluded by saved screening examples.
- Kubjas, Sodomaco and Tsigaridas, *Exact solutions in low-rank approximation
  with zeros*, https://arxiv.org/pdf/2010.15636, Introduction and Section 6;
  journal record: https://www.kaiekubjas.com/publication/kubjas-2020-exact/.
  Their rank-two NMF analysis computes critical points for small matrices and
  prescribed zero patterns. It is relevant to exact nonlinear complexity but
  supplies neither this variable-order hardness theorem nor a polynomial global
  algorithm. Do not conflate the word “exact” here with zero reconstruction error.
- Gillis, Saha, Sicilia and Vandaele, *On the Complexity of Entrywise Power
  Matrix Factorization*, https://arxiv.org/html/2607.04875v1, Definition 4.1 and
  Theorem 4.2: rank-two hardness concerns ||X-|WH|^{circ p}||_F^2 with signed W,H.
  In the displayed completeness construction, I-by-C and I-by-C' blocks can
  contain negative products before the absolute value. Entrywise modulus can
  increase ordinary rank. Even p=1 therefore does not establish standard NMF
  hardness. Their Cut-Norm/replicated-anchor mechanism differs from the present
  near-projector perturbation. This comparison checks the theorem's hypotheses,
  not an independent audit of their proof.
- Orthogonal and symmetric NMF papers connect clustering objectives with added
  constraints. Search results found *Hierarchical community detection via
  rank-2 symmetric nonnegative matrix factorization* at
  https://pmc.ncbi.nlm.nih.gov/articles/PMC5732610/, but direct access returned
  a browser challenge. Its full proof is not claimed as inspected. The current
  theorem must treat unrestricted asymmetric products, as its stability lemma
  explicitly does; known constrained hardness alone would not suffice.

Actual queries included:
`nonnegative low rank approximation identity perturbation NP hard rank two clustering`;
`nonnegative rank 2 approximation spectral clustering normalized cut complexity`;
`"nonnegative" "rank two" "NP-hard" identity`;
`"nonnegative" "rank-2" "NP-hard" approximation identity projector`;
`"nonnegative matrix" "rank two" "hardness" 2026`;
`"nonnegative low-rank approximation" "sparsest cut"`;
`nonnegative matrix factorization diagonal shift orthogonality NP hardness fixed rank`;
`"Exact solutions in low-rank approximation with zeros" arxiv`;
and `"On the Complexity of Entrywise Power Matrix Factorization"`.

The discrete NAE and weighted-cut devices and the singular-value projection
principle are standard, not claimed as invented here. The candidate contribution
is a quantified all-witness rounding lemma for nonnegative near-projectors and
its gap-preserving composition for the unrestricted rank-two objective. Independent
review must assess both this claim and overlooked equivalent formulations.
Unindexed work, complete citation descendants, and the inaccessible symmetric-NMF
article remain outside coverage. Human expert mathematical and priority review
would still be needed after an agent advance.

## Independent audit update

The complete-rule review and follow-up advanced the repaired rule. The current
entrywise-power revision is v2 (9 July 2026), titled *On the Complexity of
Low-Rank Matrix Signing and Entrywise Power Matrix Factorization*,
https://arxiv.org/html/2607.04875v2, Section 4, Theorem 4.1. Its signed-factor
absolute-power model remains distinct from ordinary NMF. The manuscript cites
this revision. Lindy et al. Lemma 2.3 and Theorem 2.4 are credited for related
extremal-coordinate geometry; novelty concerns the quantitative synthesis.

The independent reviewer additionally inspected Asteris, Papailiopoulos and
Dimakis (2015), equation (1), Section 1 and Theorem 2,
https://papers.nips.cc/paper/2015/file/eae27d77ca20db309e056e3d2dcd7d69-Paper.pdf,
and Kuang, Ding and Park (2012), Sections 1–2,
https://faculty.cc.gatech.edu/~hpark/papers/DaDingParkSDM12.pdf. The former
imposes orthonormality and gives an additive approximation guarantee; the latter
ties the factors in symmetric NMF. Neither directly subsumes this unrestricted
exact-threshold rule. See [the full audit](../history/campaign/reviews/complete-rule/review.md).
Human expert priority assessment remains necessary.
