# Nonnegative rank-two approximation: status and endpoint audit

Screened 2026-09-16. Hold; no campaign admitted.

## Prospective decision language

Input: a nonnegative rational m-by-n matrix X and a nonnegative rational
threshold tau, both explicitly encoded in binary. Ask whether nonnegative real
matrices W (m-by-2) and H (2-by-n) satisfy

    sum_ij (X_ij - (WH)_ij)^2 <= tau.

The factors have inner dimension at most two; zero columns or rows are permitted.
Input rank is unrestricted. The research target would be an original deterministic
polynomial-time Karp reduction from an NP-hard language, with polynomial witness
recovery from every valid target solution under a specified finite representation.
No such map or recovery route has been established here. Real feasibility alone
does not supply the repository's finite witness-testing contract.

Lindy, Noferini and Van Dooren,
[On rank-2 Nonnegative Matrix Factorizations and their variants](https://arxiv.org/html/2507.20612v1),
v1 July 28, 2025, Section 1, explicitly leave hardness of rank-two approximation
open. The paper uses the Frobenius norm, gives a parametrization of exact rank-two
factorizations in Section 2, and proposes suboptimal approximation and ANLS
initialization in Sections 3–4. Those algorithms are not global decision algorithms.

## A conflicting external status label

The retrieved [OpenProblemsInNLA catalogue](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/CATALOG.md)
labels NM-03 solved. However, its retrieved [individual record](https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/nonnegative-and-positive-factorizations/NM-03/README.md)
labels the question partially resolved, dates its check September 10, 2026,
and states that no unrestricted decision classification was located. It discusses
a tractable SVD subclass. These observations are conflicting retrieved page
contents, not a synchronized repository audit; caching or updates could explain
them. No solution proof was obtained from this lead. Neither the catalogue label
nor the individual record is treated as decisive primary evidence of current status.

## Immediate route boundary

Zero-error instances cannot support the sought hardness proof unless P=NP.
For tau=0, the predicate is exactly nonnegative rank(X) <= 2. For nonnegative
matrices this is equivalent to ordinary rank(X) <= 2, by the rank equality
recalled in the primary paper's Section 1. Exact rational rank is polynomial-time
computable. Thus a direct exact-factorization encoding with zero error cannot
be the missing mechanism. Positive error requires a proof controlling all
nonnegative rank-two approximants, not just intended factorizations.

Integer factorization, imposed affine entry constraints, symmetric Gram
factorization, and variable inner dimension are different targets. Search results
for Gouveia and Wiebe's [integer rank-two problem](https://arxiv.org/abs/2602.05957)
were identified but not used to infer this problem's complexity.

## Search coverage and next action

Queries included `"On rank-2 Nonnegative Matrix Factorizations" arxiv`,
`"rank-2" "nonnegative" "NP-hard" approximation`, and
`"rank-two" "nonnegative" "complexity"`.
The primary preprint and the conflicting external records were inspected;
no complete follow-up or equivalence search has been performed. Gate 1 remains
on hold. Difficulty and importance of a supported new contribution are not
assessed. No experiment, formal round, or shared experience entry was generated.

Next useful task: inspect positive-error hardness constructions for nearby
factorization problems, checking whether their mechanism fundamentally requires
negative input entries or additional components. Avoid zero-threshold encodings
and do not infer moderate difficulty merely from the fixed rank.

## Signed rank-one transfer audit, 2026-09-16

Gillis and Glineur, [Nonnegative Factorization and the Maximum Edge Biclique
Problem](https://arxiv.org/pdf/0810.4225), arXiv v1, Section 3.1 and Remark 1,
use signed input matrices with entries 1 and -d. Their factors are nonnegative,
but their inputs need not be. Remark 1 discusses the difficulty of completing
a missing factor from a signed residual; it does not establish hardness of
unconstrained rank-two approximation of nonnegative input. The author's
publication page identifies a later 2014 journal treatment; its full proof has
not yet been inspected here.

A proposed elementary transfer is to add a uniform nonnegative rank-one offset
and allow a second nonnegative component, keeping the squared-error threshold.
One intended solution would represent the offset with the additional component.
That gives only a forward construction, not a restriction on all target factors.

A counterexample to this transfer uses

    M = [[1, -4], [-4, 1]],  tau = 32.

For every nonnegative rank-at-most-one matrix Y,

    ||M-Y||_F^2 = 32 + ||I-Y||_F^2 + 8(Y_12+Y_21) >= 33.

The last bound follows because the best unrestricted rank-one approximation
error to the two-by-two identity is 1. The bound is attained at diag(1,0),
so the source optimum is exactly 33 and the threshold instance is NO.
For any uniform shift c >= 4, however,

    X = M + c J = [[1+c, c-4], [c-4, 1+c]]

is nonnegative and has a nonnegative two-component exact factorization W=X,
H=I. Its optimum is zero, so the unchanged threshold yields YES. Subtracting
the source's constant negative-entry penalty 32 from the threshold also leaves
this target YES at threshold zero. This is an elementary all-c counterexample,
not a numerical local-optimization result. It has not received independent review.

The extra component need not represent the proposed offset; subtracting cJ
from an arbitrary target product neither preserves rank one nor nonnegativity.
The example excludes the stated shift-and-increase-rank map, not all gadgets
that enforce a specific component or other threshold transformations.

The next missing mechanism is therefore a polynomial-size, nonnegative input
construction that forces the offset component, with a quantitative error bound
and recovery from every admissible target factorization. No such construction
has been found. Keep this candidate on hold rather than treating signed-input
hardness as a solution. No experimental or formal campaign rounds were run.
No shared experience entry was created; this specific failed transfer and its
proof remain with the candidate record.

Additional queries: `rank one nonnegative approximation negative matrix NP hard
Gillis Glineur 2010`, `rank two nonnegative approximation shift rank one NP hard`,
and `"Nonnegative Factorization and The Maximum Edge Biclique Problem" arxiv`.

## Exact bordered-anchor obstruction, 2026-09-16

A follow-up tests whether a scalar anchor and constant border force the intended
nonnegative offset component. For any positive rational s, use

    X_s = [[4s^2, 4s, 4s], [4s, 5, 0], [4s, 0, 5]].

This borders the shifted counterexample above. Consider the nonnegative factors

    W_s = [[s/2, s/2], [1, 0], [0, 1]],
    H_s = [[4s, 13/2, 3/2], [4s, 3/2, 13/2]].

Their product agrees exactly with the entire first row and column of X_s.
The lower-right block is [[13/2,3/2],[3/2,13/2]], so total squared error is 9.
At threshold 32 the target is YES, whereas the signed rank-one source above
has optimum 33. Subtracting the border's Schur offset 4J leaves

    [[5/2, -5/2], [-5/2, 5/2]],

a signed rank-one matrix. Thus exact border fitting enforces a rank-one residual,
but not its nonnegativity. The factors mix the offset and residual; the offset
is not forced to coincide with either nonnegative component.

This is a symbolic counterexample for every positive s. The
[Fraction checker](nonnegative-bordered-offset-probe.py) verifies factor
nonnegativity, exact border matching, error 9 and the residual at s=1,2,10,10^6;
[output](nonnegative-bordered-offset-probe.json). The calculation does not use
local optimization and does not establish the target's optimum, which is not
needed for a feasible YES witness. No independent review was requested.

Increasing s cannot remove this witness. Adding weights only to the existing
border residuals also cannot remove it, because those residuals are zero.
This excludes this one-anchor repair, not different gadgets or threshold rules.
The previously recorded L1 pin-weight conflict was inspected but not applied:
its hypothesis concerns nonzero pin errors, whereas this witness fits all pins
exactly. A viable next mechanism must enforce nonnegativity of the residual,
not merely its rank or the numerical accuracy of the border.

Experience extraction: one new
[exact-border residual entry](../experience/exact-nonnegative-borders-allow-signed-residuals.md),
zero existing entries updated, zero pending. No formal campaign rounds.


## Importance reassessment, 2026-09-16

Priority: first for a focused feasibility investigation, not admitted to a
moderate-difficulty campaign. Importance is high for the numerical-linear-algebra
boundary; difficulty is high/uncertain because no surviving forcing mechanism
or finite arbitrary-witness recovery contract has been established.

The significance is specific to the standard squared-Frobenius objective on
nonnegative input, not merely to the popularity of NMF. Section 1 of
[Lindy, Noferini and Van Dooren](https://arxiv.org/html/2507.20612v1) explicitly
separates easy rank one from unresolved rank two and investigates global
approximation through suboptimal initialization. Their arXiv record was rechecked.
The authors' [ILAS 2025 abstract](https://ilas2025.tw/files/ILAS2025-program.pdf),
“Nonnegative rank-2 approximations – on choosing a starting point for ANLS,”
also identifies this complexity gap. Independently of the open-status claim,
[Fast Rank-2 Nonnegative Matrix Factorization for Hierarchical Document Clustering](https://www.cc.gatech.edu/~hpark/papers/hierNMF2.pdf),
Introduction and Section 6, uses repeated rank-two splits as a concrete algorithmic
primitive. This supports relevance beyond a constructed restriction.

A hardness theorem would delimit global optimization of that primitive; it would
not show that local methods perform poorly on ordinary data or establish an
approximation lower bound without a quantitative gap proof. Exact zero-error
factorization remains easy. Constrained nonnegative Gram feasibility is a
different problem: extra affine constraints cannot be silently imported.

Recheck queries: `"rank-2" "nonnegative" "hardness" approximation`,
`"rank-2" "nonnegative" "NP-hard" 2026 approximation`, and the exact paper title.
No matching resolution was identified in this bounded search. The conflicting
external catalogue is not primary evidence. Next: audit a finite certificate
and recovery representation, then seek a positive-error construction controlling
the residual sign. The saved uniform-shift and exact-border counterexamples
remain exclusions; no new experiment or research round occurred.
