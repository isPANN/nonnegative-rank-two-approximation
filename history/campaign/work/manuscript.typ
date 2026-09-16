#import "report.typ": research-report
#show: research-report.with(
  title: "NP-hardness of rank-two nonnegative matrix approximation",
  date: "September 16, 2026",
  status: "Working manuscript · awaiting human expert review",
)
#set math.equation(numbering: "(1)")
#let tr = math.op("tr")
#let rk = math.op("rank")
#let cut = math.op("cut")
#let diag = math.op("diag")
#let dist = math.op("dist")

#heading(numbering: none)[Abstract]
We give a deterministic polynomial-time reduction from 3-SAT to deciding whether a nonnegative rational matrix admits a nonnegative factorization of inner dimension two within a rational squared-Frobenius error threshold. The nontrivial outputs are strictly positive symmetric matrices, but the feasible factors are unrestricted and their products may be asymmetric. The construction perturbs the identity by an all-ones matrix and a much smaller graph matrix. A quantitative stability argument forces every threshold-feasible product close to a two-block averaging projector. A rational cut gap then gives soundness, and first-row comparisons recover a satisfying assignment from every finitely encoded algebraic target witness in polynomial time. The result concerns exact threshold complexity; it does not establish NP membership or practical difficulty at fixed numerical precision.

= Introduction

Nonnegative matrix factorization approximates nonnegative data by a product of two nonnegative matrices. Fixing the inner dimension to two gives the first nontrivial approximation problem. Recent work develops its geometry and numerical initialization while explicitly leaving its NP-hardness open [1, §1]. Resolving this case distinguishes an obstruction to exact global optimization from the quality of particular local algorithms.

The distinction between approximation and exact factorization is essential here. A nonnegative matrix of ordinary rank at most two admits a nonnegative factorization of that rank [1, §2]. Our input matrices need not have rank two: the decision concerns a prescribed, generally positive reconstruction error. Algebraic analyses of small rank-two approximation problems [3, §6] likewise do not settle complexity when the matrix order grows.

*Theorem 1 (main result).* There is a deterministic polynomial-time many-one reduction
$ "3-SAT" <=_p cal(N)_2, quad
cal(N)_2 = { (X,tau) : exists W >= 0, H >= 0, norm(X-W H)_F^2 <= tau }, $
where the input has rational $X >= 0$ and $tau >= 0$, and the factors have inner dimension two. For source length $s$, the output has $O(s^2 log(s+2))$ bits. Every valid target witness encoded by dense real-algebraic coordinates yields a satisfying source assignment in time polynomial in the source and witness lengths.

The proof combines a discrete cut construction with a quantitative rounding argument for nearly optimal nonnegative matrices. The output has the form
$ X = I + epsilon J + delta A, quad 0 < delta << epsilon << 1, $ <form>
where $J$ is the all-ones matrix and $A$ is nonnegative, symmetric, and has constant row sums. Near-optimality at $I+epsilon J$ constrains a two-dimensional column space. Nonnegativity then constrains one direction in that space to nearly two coordinate levels. These levels determine a cut. The smaller perturbation records its density, with scales chosen to preserve an exact rational gap.

Earlier hardness results require different feasible sets. Gillis and Glineur's nonnegative-factor model uses signed input data [2, §3.1]; it does not give the present nonnegative-input result. The rank-two entrywise-power hardness theorem permits signed products followed by absolute values [4, Theorem 4.1]. Those absolute values cannot simply be removed. Our contribution is the quantitative rounding and gap-preserving construction for ordinary nonnegative factors. The endpoint geometry is related to [1, Lemma 2.3 and Theorem 2.4]; we do not claim the individual spectral or variance identities as new.

= Definitions and witness convention

All rational input numbers use binary encoding. The source lists its variables explicitly and has clauses of at most three signed literals. An empty conjunction is true and an empty clause is false. For the target, $X$ is a nonempty $m times n$ matrix, $W$ has size $m times 2$, and $H$ has size $2 times n$. The inequalities $W,H >= 0$ are entrywise. A zero component is allowed.

A supplied algebraic coordinate is encoded either as a rational number or as a dense integer polynomial together with the index of one of its distinct real roots. This is a witness interface, not a restriction of the target to rational feasibility. Nonempty semialgebraic sets over the rationals have real-algebraic points. No polynomial bound on witness size for arbitrary target instances is assumed.

For a symmetric nonnegative integer matrix $C$ with zero diagonal and a nontrivial partition $S,T$ of its indices, put
$ a=|S|, quad b=|T|, quad n=a+b, quad
cut_(C)(S)=sum_(i in S,j in T) C_(i j), quad rho_(C)(S)=frac(cut_(C)(S),a b). $
Each undirected crossing edge is counted once. Let $P_S$ denote the orthogonal projector onto vectors constant on each of $S,T$. Its within-block entries are $1/a$ and $1/b$; its other entries are zero. Thus $P_S >= 0$, $rk(P_S)=2$, and $P_S bold(1)=bold(1)$.

= From 3-SAT to a weighted cut threshold

We first give a self-contained discrete reduction. Its Boolean and matching devices are standard; the matrix rounding argument will carry the contribution.

== Literal graph

Pad each nonempty clause to three literals by repetition. For a clause $(ell_1,ell_2,ell_3)$ introduce a fresh variable $z$ and replace it by
$ "NAE"(ell_1,ell_2,z), quad "NAE"(not z,ell_3,f), $
where $f$ is one shared new variable and NAE requires a nonmonochromatic triple. Orient an assignment so that $f$ is false. If the first two literals agree, the first triple forces $z$ to their opposite value, and the second triple excludes exactly the all-false original clause. If they differ, a value of $z$ satisfying the second triple always exists. Complementing every value preserves NAE, so the orientation loses no witnesses.

Let $v$ be the number of original and auxiliary variables and $t$ the number of NAE clauses. Construct a graph $B$ with positive and negative literal vertices for every variable. Put weight $p_0=2t+1$ on each variable pair. Add a unit triangle for each NAE clause, discarding loops and adding parallel weights. A literal triangle contributes either zero or two to any cut, including triples with repeated endpoints. Consequently
$ K=p_0 v+2t $ <literal-threshold>
is an upper bound on every cut weight. A cut reaches $K$ if and only if it separates every variable pair and satisfies every NAE clause. Orienting the resulting values relative to the positive literal of $f$ recovers the original SAT assignment.

== Heavy mates and complementary weights

#block(breakable: false)[
Write $h=|V(B)|$ and let $E$ be the sum of its undirected edge weights. Add a mate for each vertex, join each pair by an edge of weight
$ M=h(h+1)(E+1), $
]
and retain $B$ on the original vertices. Denote this graph by $G$; its order is $n=2h$. @matching shows the construction for a path.

#figure(image("figures/matching.svg", width: 100%), caption: [The matching construction for an original four-vertex path $B$. Solid edges have their original weights; dashed edges have weight $M$. Filled and unfilled vertices show a balanced cut separating every mate pair. Only the displayed edges belong to $G$. The later complement has capacity $M$ on every distinct vertex pair.]) <matching>

*Lemma 2 (forced balance).* Every cut in $G$ with density at least $M/h$ is balanced and separates every mate pair.

*Proof.* An unbalanced cut with $a<h<b$ crosses at most $a$ matching edges. Its density is at most $M/b+E/(a b)$. Since $b>=h+1$, the deficit between $M/h$ and $M/b$ is at least $M/(h(h+1))=E+1$, whereas $E/(a b)<=E$. A balanced cut missing a mate edge has weight at most $M(h-1)+E<M h$ and therefore density below $M/h$. #h(1fr)$square$

For a balanced mate-separated cut, the density equals $M/h+frac(cut_(B)(S ∩ V(B)),h^2)$. Complement the weights by setting
$ C_(i j)=cases(M-G_(i j) quad & i!=j, 0 quad & i=j), quad
k=M-M/h-K/h^2. $ <complement>
Here $G_(i j)$ denotes an edge weight, with zero for an absent edge. The choice of $M$ exceeds every original weight, so $C>=0$. Complementation changes density to $M-rho_(G)(S)$. Lemma 2 now proves that a cut of density at most $k$ exists exactly when the source is satisfiable; every such cut recovers a satisfying assignment. In these graphs, $K<=E$ because each NAE triangle has at least two distinct vertices. The formulas give $0<=k<=max_(i j) C_(i j)=M$.

= The rational matrix map

The following construction applies to the weighted cut instances just obtained. Let
$ d=max_i sum_j C_(i j), quad
A=C+diag(d-sum_j C_(i j)). $
#block(breakable: false)[
The matrix $A$ is symmetric, nonnegative, and has row sum $d$. If $q$ is the denominator of $k$ in lowest terms, define
$ g=frac(1,q n^2), quad
L=1+n+sum_(i j) A_(i j)+2d+n(max_(i j) C_(i j)+1), $ <gap>
$ r=frac(g,16L n), quad epsilon=frac(r^2,256n^2), quad
 delta=frac(epsilon^3,144L). $ <scales>
]
Output the matrix in @form and the threshold
$ tau=n-2+2delta[tr(A)-2d+n(k+g/2)]+delta^2 norm(A)_F^2. $ <threshold>
All these numbers are rational. For nontrivial sources $n>=3$, every entry of $X$ is positive, and $tau>0$. Directly from the definitions,
$ norm(A)_F <= L, quad |tr(A)-2d+n(k+g/2)| <= L, quad
 epsilon n <= 1, quad delta L <= 1. $ <bounds>
In fact $delta L=epsilon^3/144$ is small enough that @threshold lies between zero and $n+1$.

== Completeness

For a cut $S,T$, set $Y_S=P_S+epsilon J$. It has nonnegative factors: a row of $W$ is $(1,0)$ on $S$ and $(0,1)$ on $T$; row one of $H$ has value $1/a+epsilon$ on $S$ and $epsilon$ on $T$, with the symmetric prescription for row two. These factors are rational.

Constant row sums give the trace and loss identities
$ tr(P_S A)=2d-n rho_(C)(S), $ <trace>
$ norm(X-Y_S)_F^2=n-2+2delta[tr(A)-2d+n rho_(C)(S)]+delta^2 norm(A)_F^2. $ <canonical>
To see the first identity, the within-$S$ sum is $a d-cut_(C)(S)$, and the analogous sum on $T$ is $b d-cut_(C)(S)$. For the second identity, expand $X-Y_S=I-P_S+delta A$ and use $norm(I-P_S)_F^2=n-2$. Thus every cut with density at most $k$ yields an accepted target witness.

= Stability of arbitrary nonnegative products

Completeness alone does not exclude a better asymmetric product unrelated to a cut. We now control every nonnegative rank-two matrix sufficiently close to the best rank-two error at the base matrix $X_0=I+epsilon J$.

*Lemma 3 (two-block stability).* Suppose $n>=3$, $0<epsilon n<=1$, and $Y>=0$ has rank at most two. If
$ norm(X_0-Y)_F^2 <= n-2+eta, quad
0<eta<min(1,2epsilon n+epsilon^2 n^2), $
then there is a nontrivial partition $S,T$ such that
$ norm(Y-(P_S+epsilon J))_F <= t+4n sqrt(epsilon+t), quad
 t=3sqrt(frac(eta,epsilon n)). $ <stability>

*Proof.* Put $u=bold(1)/sqrt(n)$. The squared singular values of $X_0$ are $(1+epsilon n)^2,1,dots,1$. Every rank-at-most-two approximation has squared error at least $n-2$, and every rank-one approximation has error at least $n-1$. Hence $rk(Y)=2$.

Let $P$ project onto the column space of $Y$, and set $theta=norm((I-P)u)_2$. Orthogonal projection decomposes the error exactly:
$ norm(X_0-Y)_F^2=n-2+(2epsilon n+epsilon^2 n^2)theta^2+norm(P X_0-Y)_F^2. $ <projection>
#block(breakable: false)[
This follows also from $X_0^2=I+(2epsilon n+epsilon^2 n^2)u u^T$. Choose a unit vector $v$ in the range of $P$ perpendicular to $u$, and put $Q=u u^T+v v^T$. The planes share $v$, and their other directions differ by sine $theta$. Therefore $norm(P-Q)_F=sqrt(2)theta$. Using $norm(X_0)_2<=2$ and @projection gives
$ norm(Y-(Q+epsilon J))_F
 <= sqrt(eta)+2sqrt(frac(eta,epsilon n)) <= t. $ <plane>
]
No symmetry of $Y$ was used.

Write $min_i v_i=-alpha$ and $max_i v_i=beta$. Both $alpha$ and $beta$ are positive because $sum_i v_i=0$ and $norm(v)_2=1$. The entry joining these extrema in $Q+epsilon J$ is $1/n-alpha beta+epsilon$. Entrywise nonnegativity of $Y$ and @plane imply $alpha beta<=1/n+epsilon+t$. Expanding the endpoint distances gives
$ sum_(i) (v_i+alpha)(beta-v_i)=n alpha beta-1 <= n(epsilon+t). $ <endpoints>
The identity is illustrated in @endpoint. Every summand is nonnegative and dominates the square of the distance to the closer endpoint.

#figure(image("figures/endpoint.svg", width: 92%), caption: [Schematic endpoint argument. The arch is the nonnegative function $(x+alpha)(beta-x)$ on $[-alpha,beta]$; horizontal point locations represent coordinates of $v$. A small sum in @endpoints confines each coordinate to an endpoint neighborhood. The diagram is conceptual, with no empirical data or fitted scale.]) <endpoint>

Round every coordinate of $v$ to its closer endpoint, obtaining $w$. A conservative bound from @endpoints is $norm(v-w)_2<=n sqrt(epsilon+t)$. Both levels occur because the extrema round to themselves. Center $w$ to obtain a nonzero vector $z$, and normalize it to $v_0=z/norm(z)_2$. Centering is a contraction fixing $v$, and the reverse triangle inequality gives
$ norm(v-v_0)_2 <= 2norm(v-z)_2 <= 2n sqrt(epsilon+t). $
The span of $bold(1)$ and $w$ is exactly the two-block constant subspace. Hence $P_S=u u^T+v_0 v_0^T$. Since $norm(v v^T-v_0 v_0^T)_F<=2norm(v-v_0)_2$, combining this bound with @plane proves @stability. #h(1fr)$square$

= Soundness and witness recovery

Let $Y=W H$ be any accepted target product. It is nonnegative and has rank at most two. By the triangle inequality, @threshold, and @bounds,
$ norm(X_0-Y)_F^2 <= (sqrt(tau)+delta L)^2 <= n-2+4n delta L. $ <base-excess>
For detail, writing $c=delta L<=1$, the excess is at most $(2+2n)c+2c^2<=4n c$ for $n>=3$, because $sqrt(tau)<=sqrt(n+1)<=n$.

Apply Lemma 3 with $eta=4n delta L$. The scales in @scales give $eta<1$ and $eta<2epsilon n+epsilon^2 n^2$. They also give
$ t=6sqrt(delta L/epsilon)=epsilon/2, quad
norm(Y-(P_S+epsilon J))_F <= epsilon+8n sqrt(epsilon)
=epsilon+r/2 <= 3r/4 < r < frac(1,2n). $ <rounding-radius>
Here $epsilon<=r/4$ follows directly from @scales. All estimates concern arbitrary accepted products, including asymmetric or nonoptimal ones.

== Excluding rejected cuts

Expand the loss around $X_0$ and use the universal rank-two lower bound $norm(X_0-Y)_F^2>=n-2$. Replacing $Y$ by $P_S+epsilon J$ in the cross term changes it by at most $2delta L r$. Thus
$ norm(X-Y)_F^2 >= n-2+2delta[tr(A)-2d+n rho_(C)(S)]
 +delta^2 norm(A)_F^2-2delta L r. $ <sound-loss>
If $rho_(C)(S)>k$, the integer cut numerator and $a b<=n^2$ imply $rho_(C)(S)>=k+g$. Subtracting @threshold from @sound-loss then leaves at least
$ delta n g-2delta L r > 0, $
contradicting acceptance. Therefore every accepted product determines a cut of density at most $k$, which recovers a satisfying assignment by the discrete construction.

== Deterministic extraction

The extractor need not compute a column space or a singular vector. Reconstruct $epsilon$ and $n$ from the source, and compute the first row of the supplied product. Put index $j$ in the block of index one exactly when
$ W_(1 1)H_(1 j)+W_(1 2)H_(2 j) > epsilon+frac(1,2n). $ <extract>
Within this block the reference matrix $P_S+epsilon J$ has entries at least $epsilon+1/n$; across blocks it has entries $epsilon$. The strict error bound in @rounding-radius proves that @extract separates them. @block shows this separation for the reference matrix.

#figure(image("figures/block-rounding.svg", width: 100%), caption: [First-row recovery for a two-block reference matrix. Left: $P_S$ for block sizes $a=2$, $b=4$. Right: the first row of $P_S+epsilon J$, with illustrative $epsilon=0.05$. The dashed line is $epsilon+1/(2n)$. In the reduction, the smaller exact scales in @scales and the error bound in @rounding-radius preserve every comparison.]) <block>

Restrict the recovered cut to the original literal vertices. A source variable is true exactly when its positive literal is on the opposite side from the positive literal of $f$. This completes forward construction and backward recovery as one rule.

An empty conjunction maps to the one-by-one zero matrix with threshold zero; return the all-false assignment. An empty clause, or a malformed source encoding, maps to $(I_3,0)$, which is NO by rank. These exceptional cases complete the reduction without affecting hardness on nontrivial sources.

= Encoding size and running time

#block(breakable: false)[
Let $s$ be the explicitly listed source length. The graph and scale bounds are
$ v,h,n=O(s), quad E=O(s^2), quad M=O(s^4), quad d=O(s^5), $
$ L=O(s^6), quad q=O(s^2). $
]
The denominator bound follows from @complement. All subsequent scales use fixed powers of polynomially bounded integers. Each scalar therefore has $O(log(s+2))$ bits, and the $O(s^2)$ matrix entries use $O(s^2 log(s+2))$ bits in total. Direct rational arithmetic takes polynomial time; $O(s^6)$ is a conservative bit bound for the forward map. Canonical YES factors also have polynomial bit size.

For recovery, each comparison in @extract involves at most four supplied algebraic numbers and one rational threshold. Dense coefficient lists bound each degree by its encoding length. A constant number of algebraic arithmetic and sign operations has polynomial degree and coefficient growth, and standard univariate real-root isolation and comparison run in polynomial bit time. There is no need to construct a field containing all matrix coordinates. The $O(s)$ comparisons and deterministic reconstruction therefore take time polynomial in the source and supplied witness lengths. The implementation uses exact algebraic arithmetic; it invokes no SAT or nonlinear decision solver during recovery.

= Scope of the result

The theorem establishes exact threshold NP-hardness for the standard unweighted Frobenius objective at inner dimension two. In particular, nonnegative input data and a fixed number of components do not suffice for polynomial-time exact global optimization unless P equals NP. The construction uses symmetric positive data while permitting arbitrary nonnegative factors, so it is not a hardness statement for a separately constrained symmetric or orthogonal factorization model.

The scales deliberately separate fine rational differences. We make no constant-factor inapproximability claim and no assertion that ordinary numerical tolerances expose these worst-case instances. We also do not claim NP membership of the general target language. The literature comparison supports a candidate resolution of the open rank-two hardness question in [1]; priority remains subject to a broader human expert assessment.

#heading(numbering: none)[References]
#set par(first-line-indent: 0pt)
[1] Etna Lindy, Vanni Noferini, and Paul Van Dooren. _On rank-2 Nonnegative Matrix Factorizations and their variants._ arXiv:2507.20612v1, 2025. #link("https://arxiv.org/abs/2507.20612v1")[arXiv record].

[2] Nicolas Gillis and François Glineur. _Nonnegative Factorization and the Maximum Edge Biclique Problem._ arXiv:0810.4225. #link("https://arxiv.org/abs/0810.4225")[arXiv record].

[3] Kaie Kubjas, Luca Sodomaco, and Elias Tsigaridas. _Exact solutions in low-rank approximation with zeros._ Linear Algebra and its Applications 641, 67–97, 2022. #link("https://arxiv.org/abs/2010.15636")[arXiv:2010.15636].

[4] Nicolas Gillis, Subhayan Saha, Stefano Sicilia, and Arnaud Vandaele. _On the Complexity of Low-Rank Matrix Signing and Entrywise Power Matrix Factorization._ arXiv:2607.04875v2, 2026. #link("https://arxiv.org/abs/2607.04875v2")[arXiv record].

#pagebreak()
#set heading(numbering: "A.1.")
#set text(size: 10pt)
#set par(leading: 0.4em)
#counter(heading).update(0)
= Verification and reproducibility

Finite checks test the executable construction and recovery; they do not prove the universal stability lemma. The author checked 119 block projectors exactly, 1,330 canonical cut losses across 190 cut instances, 48,416 literal cuts for 106 formulas, and 36,830 cuts for 67 matching graphs at 290 thresholds. These are component checks, not unrestricted NMF solves.

On actual forward outputs, the prepared suite has six sources and six recoveries, with matrix order at most 28. A separately written verifier has eight sources and fourteen recoveries, with order at most 24. These suites overlap. They cover YES and NO sources, empty clauses and conjunctions, component permutations, irrational rescaling, and nonoptimal accepted factor perturbations. For nontrivial outputs, both use exact cut certificates conditioned on Lemma 3. Their agreement does not independently establish that lemma. Three tiny unrestricted algebraic target self-tests pass; an unfinished larger direct nonlinear query supplied no decision.

A native independent review derived the proof estimates separately and checked seven accepted canonical witnesses, an asymmetric nonoptimal witness, and repeated or reducible algebraic encodings. It exposed a decimal parsing limit on a valid rescaled witness. After removal of that implementation limit, fresh-process recovery passed for a factor scaling of $10^5000$ and for 5,001-digit JSON polynomial coefficients. The review advanced the repaired rule. This is an internal audit, not peer review or publication acceptance.

== Environment and commands

The recorded environment is Python 3.14.7, Z3 5.1.0, OR-Tools 9.15.6755, and SymPy 1.14.0. Typst and Poppler render the manuscript. Run the following commands from the campaign directory. The script sources and fixed finite input sets are retained; no wall-clock timeout is used.

```sh
python3 work/check.py --self-test
python3 work/check.py --candidate work/algorithm.py
python3 work/verify.py --candidate work/algorithm.py
python3 reviews/complete-rule/checks.py
python3 reviews/complete-rule/check-repair.py
```

Forward mode reads one source from standard input. Recovery mode reads a source together with a supplied target witness; it uses no saved process state:

```sh
python3 work/algorithm.py < source.json
python3 work/algorithm.py --extract < witness.json
```

The exact JSON schema is in `work/contract.md`. For example, `source.json` may contain `{"variables":[0],"clauses":[[1]]}`. A saved, fully valid recovery input is available at `reviews/complete-rule/large-valid-witness.json` and can replace `witness.json` in the second command. Its output is `[true]`.

Evidence is retained in `rounds/004/`, with independent reports and runnable checks in `reviews/complete-rule/`. The final author suite logs are `prepared-input-final.jsonl` and `verification-input-final.jsonl`; the focused repair rerun is `recovery-repair.jsonl`. The independent follow-up report and `repair-results.jsonl` document the large-coordinate regression. The campaign used four research rounds; local parsing repairs were not counted as new ideas.

To regenerate the structural vector figures and this PDF:
```sh
python3 work/figures/draw.py
typst compile work/manuscript.typ work/manuscript.pdf
```

The literature audit was performed on September 16, 2026 and records theorem locations, equivalent formulations, and unresolved coverage in `work/literature.md` and the independent review. No matching unrestricted rank-two hardness theorem was located in the inspected primary sources. Unindexed, inaccessible, and unpublished work remains outside that bounded check.
