# Round 3: encode a weighted uniform sparsest cut

## Plan

Compose the round-2 stability bound with X=I+epsilon J+delta A. For a weighted
undirected graph C, set A=C+diag(d-deg_i), d=max_i deg_i. Its row sums equal d.
Scope: derive a full map from the intermediate weighted uniform sparsest-cut
threshold language, select explicit rational scales, and check all graph cuts
for 64 unweighted four-vertex graphs at three rational thresholds. This is one
construction family, not 192 independent routes. Original 3-SAT composition
remains outside this round. Use round-2 arbitrary-witness rounding; do not assume
an optimal or symmetric NMF witness. No zero-error or signed-input transfer.

## Evidence and diagnosis

[cut_map.py](cut_map.py) implements the intermediate construction.
`python3 rounds/003/probe.py` checks 190 threshold instances (zero graph uses
only threshold zero), 1,330 canonical cut witnesses and exact parameter/loss
identities; [results](result.json). These are canonical witnesses only, not an
independent global target solve. General soundness uses round 2 as follows.

Let c(S) be cut weight, a=|S|, b=n-a, K the rational source threshold and q its
denominator. Every source NO cut has c(S)/(ab)>=K+g for g=1/(q n^2).
For its block projector P,

    tr(PA)=2d-n*c(S)/(ab).

Choose L=1+n+sum(A)+2d+n(max(C)+1), assuming 0<=K<=max(C). This bounds ||A||_F
and |tr(A)-2d+n(K+g/2)|. Set r=g/(16Ln), epsilon=r^2/(256n^2),
delta=epsilon^3/(144L), and

    tau=n-2+2delta[tr(A)-2d+n(K+g/2)]+delta^2||A||_F^2.

Tau is positive for n>=3 with these parameters. All entries are nonnegative
rationals with polynomial encoding length. On any source YES cut, the explicit
nonnegative factorization of P+epsilon J from round 1 has loss <=tau.

For ANY accepted product Y, triangle inequality yields base excess at most
eta=4n delta L: tau<=n+1, delta L<=1, and sqrt(n+1)<=n. Thus round 2 applies,
t<=epsilon, and D<=epsilon+8n sqrt(epsilon)<=3r/4<r. In particular, D<1/(2n),
so thresholding the first row recovers a nontrivial partition.

Expanding the target loss, using the universal base lower bound n-2 and the
Frobenius bound |<Y-(P+epsilon J),A>|<=Lr, gives

    loss >= n-2+2delta[tr(A)-2d+n*c(S)/(ab)]
                  +delta^2||A||_F^2-2delta Lr.

If this recovered cut were NO, the lower bound exceeds tau by at least
 delta*n*g-2delta*L*r>0, a contradiction. The same proof permits asymmetric
factors and nonoptimal witnesses. The target map contains no enforced orthogonality
or symmetry constraints. This is the first complete intermediate reduction
argument, still author-only and not a 3-SAT rule.

Experience extraction: extend pending nonnegative-projector rounding with the
quantitative perturbation applicability. A separate pending entry
`research/experience/lexicographic-nmf-cut-perturbation.md` records the graph-score
composition and exact decision-gap requirement. No shared writes or independent
review. Time/token totals unavailable.

## Next action

Supply an explicit witness-preserving 3-SAT-to-weighted-sparsest-cut composition.
Rather than rely on an uninspected source theorem, use NAE triangles for Max Cut
and a large matching to force a balanced densest cut, then complement its weights.
Check every cut on small weighted graphs; the matching-dominance premise must
cover unbalanced and unsplit-pair witnesses.
