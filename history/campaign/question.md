# 3-SAT to rank-two nonnegative Frobenius approximation

Authorized budget: twenty research rounds. Research directory:
`campaigns/nonnegative-rank-two-approximation`. All campaign writes stay here.
The user authorized exploratory research despite the route and witness-contract
holds in the [screening record](work/screening.md); its original relative links
retain their research/evidence base.

Source: 3-SAT, explicitly listed variables and clauses of at most three signed
literals. Empty clauses are false; an empty conjunction is true. Witness: a
Boolean assignment satisfying every clause.

Target: a nonempty explicitly listed nonnegative rational matrix X and a
nonnegative rational threshold tau, in binary. Decide whether there are
nonnegative real W of shape m by 2 and H of shape 2 by n with
sum_ij (X_ij-(WH)_ij)^2 <= tau. Inner dimension is at most two. No missing entries,
weights, extra affine constraints, symmetry constraints on factors, or promised
input rank. These restrictions may be properties of the constructed instances,
not changes to the target language.

Goal: an original deterministic polynomial-time Karp map from 3-SAT, with YES/NO
equivalence, polynomial output bit length, and deterministic polynomial source
witness recovery from every valid finitely encoded target witness of its outputs.
The witness representation is an obligation below, not an assumption that all
real numbers have finite representations. Use exact real-algebraic coordinates;
prove the required encoding and recovery bounds. A gap construction may provide
short rational witnesses on its YES outputs, without changing the target's real
feasibility definition or rejecting valid algebraic witnesses.

A total malformed-source mapping can use (I_3,0), a target NO. Do not substitute
signed inputs, nonnegative integer factors, constrained Gram feasibility,
variable inner dimension or weighted loss for this question. A polynomial
algorithm or a barrier may be useful evidence but is not a successful hardness
rule. Keep experimental evidence separate from a general proof.

Significance: decide global optimization complexity of the standard first
nontrivial NMF rank; not an application-specific added restriction. Primary
baseline: Lindy, Noferini and Van Dooren, arXiv:2507.20612v1, Section 1.
