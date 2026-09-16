import Definitions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open scoped BigOperators Matrix.Norms.Frobenius

namespace NMF

theorem endpoint_identity {n : ℕ} (v : Fin n → ℝ) (α β : ℝ)
    (hzero : ∑ i, v i = 0) (hunit : ∑ i, (v i) ^ 2 = 1) :
    ∑ i, (v i + α) * (β - v i) = (n : ℝ) * α * β - 1 := by
  calc
    ∑ i, (v i + α) * (β - v i) =
        ∑ i, (α * β + (β - α) * v i - (v i) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = (n : ℝ) * α * β - 1 := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, hzero, hunit, mul_zero, add_zero,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem endpoint_distance (x α β : ℝ) (hlo : -α ≤ x) (hhi : x ≤ β) :
    (x - (if x + α ≤ β - x then -α else β)) ^ 2 ≤
      (x + α) * (β - x) := by
  split_ifs with h
  · nlinarith [mul_nonneg (show 0 ≤ x + α by linarith)
      (show 0 ≤ β - x - (x + α) by linarith)]
  · nlinarith [mul_nonneg (show 0 ≤ β - x by linarith)
      (show 0 ≤ x + α - (β - x) by linarith)]

theorem endpoint_rounding {n : ℕ} (v : Fin n → ℝ) (α β κ : ℝ)
    (hzero : ∑ i, v i = 0) (hunit : ∑ i, (v i) ^ 2 = 1)
    (hlo : ∀ i, -α ≤ v i) (hhi : ∀ i, v i ≤ β)
    (hgap : (n : ℝ) * α * β - 1 ≤ κ) :
    ∑ i, (v i - (if v i + α ≤ β - v i then -α else β)) ^ 2 ≤ κ := by
  calc
    _ ≤ ∑ i, (v i + α) * (β - v i) := by
      apply Finset.sum_le_sum
      intro i _
      exact endpoint_distance (v i) α β (hlo i) (hhi i)
    _ = (n : ℝ) * α * β - 1 := endpoint_identity v α β hzero hunit
    _ ≤ κ := hgap


theorem nonnegative_endpoint_rounding {n : ℕ} (hn : 0 < n)
    (v : Fin n → ℝ) (Y : Matrix (Fin n) (Fin n) ℝ) (α β ε t : ℝ)
    (imin imax : Fin n)
    (hzero : ∑ i, v i = 0) (hunit : ∑ i, (v i) ^ 2 = 1)
    (hlo : ∀ i, -α ≤ v i) (hhi : ∀ i, v i ≤ β)
    (hmin : v imin = -α) (hmax : v imax = β)
    (hnonneg : ∀ i j, 0 ≤ Y i j)
    (hclose : ∀ i j, |Y i j - ((n : ℝ)⁻¹ + v i * v j + ε)| ≤ t) :
    ∑ i, (v i - (if v i + α ≤ β - v i then -α else β)) ^ 2
      ≤ (n : ℝ) * (ε + t) := by
  apply endpoint_rounding v α β ((n : ℝ) * (ε + t)) hzero hunit hlo hhi
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hentry := (abs_le.mp (hclose imin imax)).2
  rw [hmin, hmax] at hentry
  have hab : α * β ≤ (n : ℝ)⁻¹ + ε + t := by
    nlinarith [hnonneg imin imax]
  have hmul := mul_le_mul_of_nonneg_left hab (le_of_lt hnpos)
  have hinv : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hnpos)
  nlinarith


theorem normalize_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v z : E) (hv : ‖v‖ = 1) (hz : z ≠ 0) :
    ‖v - NormedSpace.normalize z‖ ≤ 2 * ‖v - z‖ := by
  have hnorm : ‖NormedSpace.normalize z‖ = 1 :=
    NormedSpace.norm_normalize_eq_one_iff.mpr hz
  have hdiff : z - NormedSpace.normalize z =
      (‖z‖ - 1) • NormedSpace.normalize z := by
    rw [sub_smul, one_smul, NormedSpace.norm_smul_normalize]
  have hbound : ‖z - NormedSpace.normalize z‖ ≤ ‖v - z‖ := by
    rw [hdiff, norm_smul, hnorm, mul_one, Real.norm_eq_abs]
    have h := abs_norm_sub_norm_le z v
    rw [hv, norm_sub_rev z v] at h
    exact h
  have htri := norm_add_le (v - z) (z - NormedSpace.normalize z)
  rw [sub_add_sub_cancel] at htri
  linarith

theorem frobeniusSq_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    frobeniusSq A = Matrix.trace (A.transpose * A) := by
  unfold frobeniusSq Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  exact Finset.sum_comm

theorem frobeniusSq_add_orthogonal {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (h : A.transpose * B = 0) :
    frobeniusSq (A + B) = frobeniusSq A + frobeniusSq B := by
  have h' : B.transpose * A = 0 := by
    simpa using congrArg Matrix.transpose h
  simp only [frobeniusSq_trace, Matrix.transpose_add, Matrix.add_mul,
    Matrix.mul_add, Matrix.trace_add, h, h', add_zero, zero_add]

theorem projection_error_split {n : ℕ} (X Y P : Matrix (Fin n) (Fin n) ℝ)
    (hsym : P.transpose = P) (hidem : P * P = P) (hfix : P * Y = Y) :
    frobeniusSq (X - Y) =
      frobeniusSq ((1 - P) * X) + frobeniusSq (P * X - Y) := by
  have horth : ((1 - P) * X).transpose * (P * X - Y) = 0 := by
    rw [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one, hsym,
      Matrix.mul_assoc, Matrix.mul_sub, ← Matrix.mul_assoc (1 - P) P X]
    simp [Matrix.sub_mul, hidem, hfix]
  have hsum : (1 - P) * X + (P * X - Y) = X - Y := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    abel
  rw [← hsum]
  exact frobeniusSq_add_orthogonal _ _ horth

theorem projection_base_residual {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hsym : P.transpose = P) (hidem : P * P = P) :
    frobeniusSq ((1 - P) * baseMatrix n ε) =
      (n : ℝ) - Matrix.trace P + (2 * ε + (n : ℝ) * ε ^ 2) *
        Matrix.trace ((1 - P) * (Matrix.of (fun (_ _ : Fin n) => (1 : ℝ)))) := by
  let J : Matrix (Fin n) (Fin n) ℝ := fun _ _ => 1
  let X := baseMatrix n ε
  let R := 1 - P
  have hR : R * R = R := by
    dsimp [R]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hidem]
    abel
  have hRt : R.transpose = R := by simp [R, hsym]
  have hXt : X.transpose = X := by
    ext i j
    simp [X, baseMatrix, eq_comm]
  have hX : X = 1 + ε • J := by
    ext i j
    simp [X, baseMatrix, J, Matrix.one_apply]
  have hJJ : J * J = (n : ℝ) • J := by
    ext i j
    simp [J, Matrix.mul_apply]
  have hXX : X * X = 1 + (2 * ε + (n : ℝ) * ε ^ 2) • J := by
    rw [hX]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, hJJ, smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  calc
    frobeniusSq (R * X) = Matrix.trace (X.transpose * (R * R) * X) := by
      rw [frobeniusSq_trace, Matrix.transpose_mul, hRt]
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (R * (X * X)) := by
      rw [hR, hXt, Matrix.mul_assoc, Matrix.trace_mul_comm X (R * X),
        Matrix.mul_assoc]
    _ = Matrix.trace R + (2 * ε + (n : ℝ) * ε ^ 2) * Matrix.trace (R * J) := by
      rw [hXX]
      simp [Matrix.mul_add]
    _ = _ := by
      simp only [R, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin]
      rfl

theorem projection_ones_trace {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (hsym : R.transpose = R) (hidem : R * R = R) :
    Matrix.trace (R * (Matrix.of (fun (_ _ : Fin n) => (1 : ℝ)))) =
      ∑ i, (∑ j, R i j) ^ 2 := by
  let e : Fin n → ℝ := fun _ => 1
  have hquad : dotProduct (R.mulVec e) (R.mulVec e) = dotProduct e (R.mulVec e) := by
    rw [← Matrix.dotProduct_transpose_mulVec R e (R.mulVec e), hsym,
      Matrix.mulVec_mulVec, hidem]
  simpa [e, dotProduct, Matrix.mulVec, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, pow_two] using hquad.symm

theorem projection_error_identity {n : ℕ} (hn : 0 < n)
    (Y P : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (hsym : P.transpose = P) (hidem : P * P = P) (hfix : P * Y = Y) :
    frobeniusSq (baseMatrix n ε - Y) = (n : ℝ) - Matrix.trace P +
      (2 * ε * n + ε ^ 2 * (n : ℝ) ^ 2) *
        ((∑ i, (∑ j, (1 - P) i j) ^ 2) / n) +
      frobeniusSq (P * baseMatrix n ε - Y) := by
  have hRsym : (1 - P).transpose = 1 - P := by simp [hsym]
  have hRidem : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hidem]
    abel
  rw [projection_error_split _ _ P hsym hidem hfix,
    projection_base_residual P ε hsym hidem,
    projection_ones_trace (1 - P) hRsym hRidem]
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

theorem near_optimal_projection_bounds {n : ℕ} (hn : 0 < n)
    (Y P : Matrix (Fin n) (Fin n) ℝ) (ε η : ℝ)
    (hε : 0 < ε) (hsym : P.transpose = P) (hidem : P * P = P)
    (hfix : P * Y = Y) (htrace : Matrix.trace P = 2)
    (herror : frobeniusSq (baseMatrix n ε - Y) ≤ (n : ℝ) - 2 + η) :
    frobeniusSq (P * baseMatrix n ε - Y) ≤ η ∧
      ((∑ i, (∑ j, (1 - P) i j) ^ 2) / n) ≤
        η / (2 * ε * n + ε ^ 2 * (n : ℝ) ^ 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hγ : 0 < 2 * ε * n + ε ^ 2 * (n : ℝ) ^ 2 := by positivity
  have hθ : 0 ≤ (∑ i, (∑ j, (1 - P) i j) ^ 2) / (n : ℝ) := by positivity
  have hres : 0 ≤ frobeniusSq (P * baseMatrix n ε - Y) := by
    unfold frobeniusSq
    positivity
  rw [projection_error_identity hn Y P ε hsym hidem hfix, htrace] at herror
  constructor
  · nlinarith [mul_nonneg (le_of_lt hγ) hθ]
  · apply (le_div_iff₀ hγ).mpr
    nlinarith

theorem exists_column_projection {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ,
      P.transpose = P ∧ P * P = P ∧ P * Y = Y ∧ Matrix.trace P = (Y.rank : ℝ) := by
  let K := LinearMap.range Y.toEuclideanLin
  let p : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    K.starProjection.toLinearMap
  let P : Matrix (Fin n) (Fin n) ℝ := Matrix.toEuclideanLin.symm p
  have hp : LinearMap.IsProj K p :=
    ⟨fun x => by simp [p], fun x hx => K.starProjection_eq_self_iff.mpr hx⟩
  have hP : P.toEuclideanLin = p := Matrix.toEuclideanLin.apply_symm_apply p
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · have h := Matrix.isSymmetric_toEuclideanLin_iff.mp
      (show P.toEuclideanLin.IsSymmetric by rw [hP]; exact K.starProjection_isSymmetric)
    simpa [Matrix.IsHermitian] using h
  · apply Matrix.toEuclideanLin.injective
    simp only [Matrix.toLpLin_mul_same, hP]
    exact hp.isIdempotentElem
  · apply Matrix.toEuclideanLin.injective
    simp only [Matrix.toLpLin_mul_same, hP]
    apply LinearMap.ext
    intro x
    exact hp.map_id _ ⟨x, rfl⟩
  · have htr := hp.trace
    rw [LinearMap.trace_eq_matrix_trace ℝ (PiLp.basisFun 2 ℝ (Fin n))] at htr
    have hrank : Y.rank = Module.finrank ℝ K :=
      Y.rank_eq_finrank_range_toLin (PiLp.basisFun 2 ℝ (Fin n))
        (PiLp.basisFun 2 ℝ (Fin n))
    simpa only [hrank, P, Matrix.toLpLin_eq_toLin, Matrix.toLin_symm] using htr

theorem rank_two_of_near_optimal {n : ℕ} (hn : 0 < n)
    (Y : Matrix (Fin n) (Fin n) ℝ) (ε η : ℝ) (hε : 0 ≤ ε) (hη : η < 1)
    (hrank : Y.rank ≤ 2)
    (herror : frobeniusSq (baseMatrix n ε - Y) ≤ (n : ℝ) - 2 + η) :
    Y.rank = 2 := by
  obtain ⟨P, hsym, hidem, hfix, htrace⟩ := exists_column_projection Y
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hγ : 0 ≤ 2 * ε * n + ε ^ 2 * (n : ℝ) ^ 2 := by positivity
  have hθ : 0 ≤ (∑ i, (∑ j, (1 - P) i j) ^ 2) / (n : ℝ) := by positivity
  have hres : 0 ≤ frobeniusSq (P * baseMatrix n ε - Y) := by
    unfold frobeniusSq
    positivity
  rw [projection_error_identity hn Y P ε hsym hidem hfix, htrace] at herror
  have hlower : (1 : ℝ) < Y.rank := by nlinarith [mul_nonneg hγ hθ]
  have hlower_nat : 1 < Y.rank := by exact_mod_cast hlower
  omega

theorem orthonormalBasis_first {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 2) (w : E) (hw : ‖w‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 2) ℝ E, b 0 = w := by
  let v : Fin 2 → E := fun _ => w
  have hv : Orthonormal ℝ (({0} : Set (Fin 2)).restrict v) := by
    constructor
    · intro i
      exact hw
    · intro i j hij
      exact (hij (Subtype.ext (by simpa using i.property.trans j.property.symm))).elim
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simpa using hdim)
  exact ⟨b, hb 0 (by simp)⟩

theorem plane_projection_basis {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Submodule ℝ E) (hdim : Module.finrank ℝ K = 2)
    (u : E) (hpu : K.starProjection u ≠ 0) :
    ∃ w v : E, ‖w‖ = 1 ∧ ‖v‖ = 1 ∧ inner ℝ v u = 0 ∧
      inner ℝ u w = ‖K.starProjection u‖ ∧
      (∀ x, K.starProjection x = inner ℝ w x • w + inner ℝ v x • v) := by
  let a : K := K.orthogonalProjectionOnto u
  have ha : a ≠ 0 := by
    intro h
    apply hpu
    exact congrArg Subtype.val h
  let w := NormedSpace.normalize a
  have hw : ‖w‖ = 1 := NormedSpace.norm_normalize_eq_one_iff.mpr ha
  obtain ⟨b, hb⟩ := orthonormalBasis_first hdim w hw
  refine ⟨(w : E), (b 1 : E), hw, b.orthonormal.norm_eq_one 1, ?_, ?_, ?_⟩
  · have horth : inner ℝ (b 1) w = 0 := by
      rw [← hb]
      exact b.orthonormal.inner_eq_zero (by decide)
    have hau : (a : E) = K.starProjection u := rfl
    have hinner : inner ℝ (b 1 : E) u = inner ℝ (b 1 : E) (a : E) := by
      rw [hau, ← K.inner_starProjection_left_eq_right,
        K.starProjection_mem_subspace_eq_self]
    rw [hinner]
    change inner ℝ (b 1) a = 0
    rw [← NormedSpace.norm_smul_normalize a, inner_smul_right, horth, mul_zero]
  · have hinner : inner ℝ u (w : E) = inner ℝ (a : E) (w : E) := by
      change inner ℝ u (w : E) = inner ℝ (K.starProjection u) (w : E)
      rw [K.inner_starProjection_left_eq_right, K.starProjection_mem_subspace_eq_self]
    rw [hinner]
    change inner ℝ a w = ‖a‖
    nth_rw 1 [← NormedSpace.norm_smul_normalize a]
    rw [inner_smul_left, real_inner_self_eq_norm_sq, hw]
    simp
  · intro x
    have h := b.orthogonalProjectionOnto_apply_eq_sum x
    have h' := congrArg Subtype.val h
    simpa [Fin.sum_univ_two, hb] using h'

theorem frobenius_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Real.sqrt (frobeniusSq A) = ‖A‖ := by
  simp [Matrix.frobenius_norm_def, frobeniusSq, Real.sqrt_eq_rpow]

theorem frobeniusSq_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    frobeniusSq A = ‖A‖ ^ 2 := by
  rw [← frobenius_norm, Real.sq_sqrt]
  unfold frobeniusSq
  positivity

theorem outer_norm {n : ℕ} (v w : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.vecMulVec v w‖ = ‖v‖ * ‖w‖ := by
  have hs : frobeniusSq (Matrix.vecMulVec v w) = ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
    simp only [frobeniusSq, Matrix.vecMulVec_apply, mul_pow,
      ← Finset.mul_sum, ← Finset.sum_mul, EuclideanSpace.real_norm_sq_eq]
  rw [frobeniusSq_norm] at hs
  nlinarith [norm_nonneg (Matrix.vecMulVec v w), norm_nonneg v, norm_nonneg w,
    mul_nonneg (norm_nonneg v) (norm_nonneg w)]

theorem outer_difference_sq {n : ℕ} (v w : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    frobeniusSq (Matrix.vecMulVec v v - Matrix.vecMulVec w w) =
      2 - 2 * (inner ℝ v w) ^ 2 := by
  have hv' : ∑ i, (v i) ^ 2 = 1 := by rw [← EuclideanSpace.real_norm_sq_eq, hv]; norm_num
  have hw' : ∑ i, (w i) ^ 2 = 1 := by rw [← EuclideanSpace.real_norm_sq_eq, hw]; norm_num
  have hi : inner ℝ v w = ∑ i, v i * w i := by
    simp [PiLp.inner_apply, mul_comm]
  unfold frobeniusSq
  simp only [Matrix.sub_apply, Matrix.vecMulVec_apply]
  calc
    _ = ∑ i, ∑ j, ((v i)^2 * (v j)^2 + (w i)^2 * (w j)^2 -
        2 * (v i * w i) * (v j * w j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, hv', hw', ← hi,
        mul_one, ← Finset.mul_sum]
      ring

theorem outer_difference_bound {n : ℕ} (v w : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ‖Matrix.vecMulVec v v - Matrix.vecMulVec w w‖ ≤ 2 * ‖v - w‖ := by
  have heq : Matrix.vecMulVec v v - Matrix.vecMulVec w w =
      Matrix.vecMulVec (v - w) v + Matrix.vecMulVec w (v - w) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.vecMulVec_apply, PiLp.sub_apply]
    ring
  rw [heq]
  calc
    _ ≤ ‖Matrix.vecMulVec (v - w) v‖ + ‖Matrix.vecMulVec w (v - w)‖ := norm_add_le _ _
    _ = _ := by rw [outer_norm, outer_norm, hv, hw]; ring

theorem matrix_projection_plane {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hsym : P.transpose = P) (hidem : P * P = P) (htrace : Matrix.trace P = 2)
    (u : EuclideanSpace ℝ (Fin n)) (hpu : P.toEuclideanLin u ≠ 0) :
    ∃ w v : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 ∧ ‖v‖ = 1 ∧
      inner ℝ v u = 0 ∧ inner ℝ u w = ‖P.toEuclideanLin u‖ ∧
      P = Matrix.vecMulVec w w + Matrix.vecMulVec v v := by
  let p := P.toEuclideanLin
  let K := LinearMap.range p
  have hi : IsIdempotentElem p := by
    have h := congrArg Matrix.toEuclideanLin hidem
    simp only [Matrix.toLpLin_mul_same] at h
    exact h
  have hs : p.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
    simpa [Matrix.IsHermitian] using hsym)
  obtain ⟨_, hp⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp ⟨hi, hs⟩
  have hpapp (x) : p x = K.starProjection x := congrArg (fun f : _ →ₗ[ℝ] _ => f x) hp
  have hdim : Module.finrank ℝ K = 2 := by
    have ht := (LinearMap.IsIdempotentElem.isProj_range p hi).trace
    rw [LinearMap.trace_eq_matrix_trace ℝ (PiLp.basisFun 2 ℝ (Fin n))] at ht
    have hm : LinearMap.toMatrix (PiLp.basisFun 2 ℝ (Fin n))
        (PiLp.basisFun 2 ℝ (Fin n)) p = P := LinearMap.toMatrix_toLin _ _ P
    rw [hm, htrace] at ht
    exact_mod_cast ht.symm
  obtain ⟨w, v, hw, hv, hvu, huw, hrep⟩ :=
    plane_projection_basis K hdim u (by simpa only [← hpapp] using hpu)
  refine ⟨w, v, hw, hv, hvu, ?_, ?_⟩
  · simpa only [← hpapp] using huw
  · ext i j
    have h := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z i)
      (hrep (EuclideanSpace.single j 1))
    simp only [← hpapp] at h
    simpa [p, Matrix.toLpLin_apply, EuclideanSpace.single, Matrix.mulVec_single,
      EuclideanSpace.inner_single_right, Matrix.vecMulVec_apply, mul_comm] using h

noncomputable def unitOnes (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun _ => (Real.sqrt (n : ℝ))⁻¹)

theorem unitOnes_norm {n : ℕ} (hn : 0 < n) : ‖unitOnes n‖ = 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : ‖unitOnes n‖ ^ 2 = 1 := by
    simp [EuclideanSpace.real_norm_sq_eq, unitOnes, inv_pow,
      Real.sq_sqrt (le_of_lt hnpos), ne_of_gt hnpos]
  nlinarith [norm_nonneg (unitOnes n)]

theorem unitOnes_outer {n : ℕ} (_hn : 0 < n) :
    Matrix.vecMulVec (unitOnes n) (unitOnes n) =
      (n : ℝ)⁻¹ • Matrix.of (fun (_ _ : Fin n) => (1 : ℝ)) := by
  ext i j
  simp only [Matrix.vecMulVec_apply, unitOnes,
    Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one]
  rw [← pow_two, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

theorem unitOnes_image_sq {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) :
    ‖R.toEuclideanLin (unitOnes n)‖ ^ 2 =
      (∑ i, (∑ j, R i j) ^ 2) / n := by
  simp only [EuclideanSpace.real_norm_sq_eq, Matrix.toLpLin_apply,
    unitOnes, Matrix.mulVec, dotProduct,
    ← Finset.sum_mul, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n),
    ← Finset.sum_mul, div_eq_mul_inv]

theorem matrix_projection_pythagoras {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hsym : P.transpose = P) (hidem : P * P = P)
    (u : EuclideanSpace ℝ (Fin n)) :
    ‖u‖ ^ 2 = ‖P.toEuclideanLin u‖ ^ 2 + ‖u - P.toEuclideanLin u‖ ^ 2 := by
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (show P.IsHermitian by simpa [Matrix.IsHermitian] using hsym)
  have hi : P.toEuclideanLin (P.toEuclideanLin u) = P.toEuclideanLin u := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M.toEuclideanLin u) hidem
    simpa only [Matrix.toLpLin_mul_same, LinearMap.comp_apply] using h
  have hinner : inner ℝ (P.toEuclideanLin u) u = ‖P.toEuclideanLin u‖ ^ 2 := by
    calc
      _ = inner ℝ (P.toEuclideanLin (P.toEuclideanLin u)) u := by rw [hi]
      _ = inner ℝ (P.toEuclideanLin u) (P.toEuclideanLin u) := hs _ _
      _ = _ := real_inner_self_eq_norm_sq _
  rw [norm_sub_sq_real]
  nlinarith [real_inner_comm u (P.toEuclideanLin u)]

theorem baseMatrix_eq {n : ℕ} (ε : ℝ) : baseMatrix n ε =
    1 + ε • Matrix.of (fun (_ _ : Fin n) => (1 : ℝ)) := by
  ext i j
  simp [baseMatrix, Matrix.one_apply]

theorem projection_constant_norm {n : ℕ} (hn : 0 < n)
    (P : Matrix (Fin n) (Fin n) ℝ) :
    ‖(P - 1) * Matrix.of (fun (_ _ : Fin n) => (1 : ℝ))‖ =
      n * ‖unitOnes n - P.toEuclideanLin (unitOnes n)‖ := by
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hJ : Matrix.of (fun (_ _ : Fin n) => (1 : ℝ)) =
      (n : ℝ) • Matrix.vecMulVec (unitOnes n) (unitOnes n) := by
    rw [unitOnes_outer hn, smul_smul, mul_inv_cancel₀ hnne, one_smul]
  rw [hJ, Matrix.mul_smul, Matrix.mul_vecMulVec]
  change ‖(n : ℝ) • Matrix.vecMulVec ((P - 1).toEuclideanLin (unitOnes n))
    (unitOnes n)‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n),
    outer_norm, unitOnes_norm hn, mul_one]
  congr 1
  simp [Matrix.toEuclideanLin, norm_sub_rev]

theorem near_optimal_plane {n : ℕ} (hn : 0 < n)
    (Y : Matrix (Fin n) (Fin n) ℝ) (ε η : ℝ)
    (hε : 0 < ε) (hεn : ε * n ≤ 1) (hη : 0 < η) (hηone : η < 1)
    (hgap : η < 2 * ε * n + ε ^ 2 * (n : ℝ) ^ 2)
    (hrank : Y.rank ≤ 2)
    (herror : frobeniusSq (baseMatrix n ε - Y) ≤ (n : ℝ) - 2 + η) :
    ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 ∧ inner ℝ v (unitOnes n) = 0 ∧
      ‖Y - (Matrix.vecMulVec (unitOnes n) (unitOnes n) + Matrix.vecMulVec v v +
        ε • Matrix.of (fun (_ _ : Fin n) => (1 : ℝ)))‖ ≤
        3 * Real.sqrt (η / (ε * n)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hen : 0 < ε * n := mul_pos hε hnpos
  have hr := rank_two_of_near_optimal hn Y ε η (le_of_lt hε) hηone hrank herror
  obtain ⟨P, hsym, hidem, hfix, htrace⟩ := exists_column_projection Y
  rw [hr, Nat.cast_ofNat] at htrace
  let u := unitOnes n
  let θ := ‖u - P.toEuclideanLin u‖
  let γ := 2 * ε * n + ε ^ 2 * (n : ℝ) ^ 2
  have hu : ‖u‖ = 1 := unitOnes_norm hn
  have hθsq : (∑ i, (∑ j, (1 - P) i j) ^ 2) / (n : ℝ) = θ ^ 2 := by
    rw [← unitOnes_image_sq]
    simp [θ, u, Matrix.toEuclideanLin]
  have heq := projection_error_identity hn Y P ε hsym hidem hfix
  rw [htrace, hθsq] at heq
  simp only [frobeniusSq_norm] at heq herror
  have hrespos : 0 ≤ ‖P * baseMatrix n ε - Y‖ ^ 2 := sq_nonneg _
  have hγθ : γ * θ ^ 2 ≤ η := by dsimp [γ]; linarith
  have hγpos : 0 < γ := by dsimp [γ]; positivity
  have hres : ‖P * baseMatrix n ε - Y‖ ≤ Real.sqrt η := by
    apply (Real.le_sqrt (norm_nonneg _) (le_of_lt hη)).mpr
    have := mul_nonneg (le_of_lt hγpos) (sq_nonneg θ)
    dsimp [γ] at this
    linarith
  have hpu : P.toEuclideanLin u ≠ 0 := by
    intro hz
    have hθone : θ = 1 := by simp [θ, hz, hu]
    rw [hθone] at hγθ
    dsimp [γ] at hγθ
    linarith
  obtain ⟨w, v, hw, hv, hvu, huw, hP⟩ :=
    matrix_projection_plane P hsym hidem htrace u hpu
  let Q := Matrix.vecMulVec u u + Matrix.vecMulVec v v
  let J := Matrix.of (fun (_ _ : Fin n) => (1 : ℝ))
  have hpyt := matrix_projection_pythagoras P hsym hidem u
  rw [hu] at hpyt
  have hPQ : P - Q = Matrix.vecMulVec w w - Matrix.vecMulVec u u := by
    rw [hP]
    dsimp [Q]
    abel
  have hPQsq : ‖P - Q‖ ^ 2 = 2 * θ ^ 2 := by
    rw [← frobeniusSq_norm, hPQ, outer_difference_sq w u hw hu,
      real_inner_comm u w, huw]
    dsimp [θ]
    nlinarith only [hpyt]
  have hPQbound : ‖P - Q‖ ≤ Real.sqrt (η / (ε * n)) := by
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    apply (le_div_iff₀ hen).mpr
    rw [hPQsq]
    have hterm : 0 ≤ (ε ^ 2 * (n : ℝ) ^ 2) * θ ^ 2 := by positivity
    dsimp [γ] at hγθ
    nlinarith only [hγθ, hterm]
  have hconstant : ‖ε • ((P - 1) * J)‖ ≤ Real.sqrt η := by
    apply (Real.le_sqrt (norm_nonneg _) (le_of_lt hη)).mpr
    have hc : ‖ε • ((P - 1) * J)‖ = ε * n * θ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε, projection_constant_norm hn]
      dsimp [θ, u]
      ring
    rw [hc]
    have ht : 0 ≤ (2 * ε * n) * θ ^ 2 := by positivity
    dsimp [γ] at hγθ
    nlinarith only [hγθ, ht]
  have hsmall : Real.sqrt η ≤ Real.sqrt (η / (ε * n)) := by
    apply Real.sqrt_le_sqrt
    apply (le_div_iff₀ hen).mpr
    simpa using mul_le_mul_of_nonneg_left hεn (le_of_lt hη)
  have hsplit : Y - (Q + ε • J) =
      (Y - P * baseMatrix n ε) + (P - Q) + ε • ((P - 1) * J) := by
    rw [baseMatrix_eq]
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_mul,
      Matrix.one_mul, smul_sub]
    dsimp [J]
    abel
  refine ⟨v, hv, hvu, ?_⟩
  change ‖Y - (Q + ε • J)‖ ≤ _
  rw [hsplit]
  have htri := norm_add_le ((Y - P * baseMatrix n ε) + (P - Q)) (ε • ((P - 1) * J))
  have htri' := norm_add_le (Y - P * baseMatrix n ε) (P - Q)
  rw [norm_sub_rev Y (P * baseMatrix n ε)] at htri'
  linarith

theorem inner_unitOnes {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ v (unitOnes n) = (∑ i, v i) * (Real.sqrt (n : ℝ))⁻¹ := by
  simp [PiLp.inner_apply, unitOnes, ← Finset.mul_sum, mul_comm]

theorem center_error {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v w : E) (hu : ‖u‖ = 1) (hvu : inner ℝ v u = 0) :
    ‖v - (w - inner ℝ u w • u)‖ ≤ ‖v - w‖ := by
  have heq : v - (w - inner ℝ u w • u) = (v - w) + inner ℝ u w • u := by abel
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [heq, norm_add_sq_real, inner_smul_right, inner_sub_left, hvu,
    real_inner_comm u w, norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs]
  nlinarith only [sq_nonneg (inner ℝ u w)]

theorem sum_two_levels {n : ℕ} (S : Finset (Fin n)) (c d : ℝ) :
    (∑ i, if i ∈ S then c else d) = (S.card : ℝ) * c + ((n - S.card : ℕ) : ℝ) * d := by
  classical
  rw [← Finset.sum_add_sum_compl S (fun i => if i ∈ S then c else d)]
  have h1 : (∑ i ∈ S, if i ∈ S then c else d) = ∑ _i ∈ S, c := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos hi]
  have h2 : (∑ i ∈ Sᶜ, if i ∈ S then c else d) = ∑ _i ∈ Sᶜ, d := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_neg (Finset.mem_compl.mp hi)]
  rw [h1, h2]
  simp [Finset.card_compl]

theorem two_level_projector {n : ℕ} (hn : 0 < n) (S : Finset (Fin n))
    (hSpos : 0 < S.card) (hSlt : S.card < n)
    (v : EuclideanSpace ℝ (Fin n)) (c d ε : ℝ)
    (hvalues : ∀ i, v i = if i ∈ S then c else d)
    (hzero : ∑ i, v i = 0) (hunit : ‖v‖ = 1) :
    Matrix.vecMulVec (unitOnes n) (unitOnes n) + Matrix.vecMulVec v v +
      ε • Matrix.of (fun (_ _ : Fin n) => (1 : ℝ)) = blockMatrix S ε := by
  have ha : (0 : ℝ) < S.card := by exact_mod_cast hSpos
  have hb : (0 : ℝ) < (n - S.card : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hSlt
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hab : (S.card : ℝ) + ((n - S.card : ℕ) : ℝ) = n := by
    exact_mod_cast Nat.add_sub_of_le (le_of_lt hSlt)
  have hz : (S.card : ℝ) * c + ((n - S.card : ℕ) : ℝ) * d = 0 := by
    simpa only [hvalues, sum_two_levels] using hzero
  have hq : (S.card : ℝ) * c ^ 2 + ((n - S.card : ℕ) : ℝ) * d ^ 2 = 1 := by
    have hh : ∑ i, (v i) ^ 2 = 1 := by rw [← EuclideanSpace.real_norm_sq_eq, hunit]; norm_num
    simpa only [hvalues, ite_pow, sum_two_levels] using hh
  have hcdsum := congrArg (fun x : ℝ => x * (c + d)) hz
  have habcd := congrArg (fun x : ℝ => x * c * d) hab
  have hncd : (n : ℝ) * (c * d) = -1 := by nlinarith only [hcdsum, habcd, hq]
  have hcd : c * d = -(n : ℝ)⁻¹ := by
    apply mul_left_cancel₀ hnne
    rw [hncd]
    simp [hnne]
  have hc : (n : ℝ)⁻¹ + c ^ 2 = (S.card : ℝ)⁻¹ := by
    have hc0 := congrArg (fun x : ℝ => x * c) hz
    have hc1 : (S.card : ℝ) * (c ^ 2 - c * d) = 1 := by
      nlinarith only [hc0, hncd, habcd]
    rw [hcd] at hc1
    apply mul_left_cancel₀ (ne_of_gt ha)
    rw [mul_inv_cancel₀ (ne_of_gt ha)]
    nlinarith only [hc1]
  have hd : (n : ℝ)⁻¹ + d ^ 2 = ((n - S.card : ℕ) : ℝ)⁻¹ := by
    have hd0 := congrArg (fun x : ℝ => x * d) hz
    have hd1 : ((n - S.card : ℕ) : ℝ) * (d ^ 2 - c * d) = 1 := by
      nlinarith only [hd0, hncd, habcd]
    rw [hcd] at hd1
    apply mul_left_cancel₀ (ne_of_gt hb)
    rw [mul_inv_cancel₀ (ne_of_gt hb)]
    nlinarith only [hd1]
  rw [unitOnes_outer hn]
  ext i j
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp [blockMatrix, hvalues, hi, hj, Matrix.vecMulVec_apply, ← pow_two, hc, hd,
      hcd, mul_comm, add_comm]

theorem entry_le_frobenius {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    |A i j| ≤ ‖A‖ := by
  have hrow : (A i j) ^ 2 ≤ ∑ k, (A i k) ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (A i k)) (Finset.mem_univ j)
  have hall : (∑ k, (A i k) ^ 2) ≤ frobeniusSq A :=
    Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (A k l)))
      (Finset.mem_univ i)
  rw [frobeniusSq_norm] at hall
  nlinarith only [hrow, hall, sq_abs (A i j), abs_nonneg (A i j), norm_nonneg A]

theorem extrema_strict {n : ℕ} (hn : 0 < n) (v : EuclideanSpace ℝ (Fin n))
    (hzero : ∑ i, v i = 0) (hunit : ‖v‖ = 1) :
    ∃ imin imax : Fin n, (∀ i, v imin ≤ v i) ∧ (∀ i, v i ≤ v imax) ∧ v imin < v imax := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨imin, _, hlo⟩ := Finset.univ.exists_min_image (fun i => v i) Finset.univ_nonempty
  obtain ⟨imax, _, hhi⟩ := Finset.univ.exists_max_image (fun i => v i) Finset.univ_nonempty
  have hl (i) := hlo i (Finset.mem_univ i)
  have hh (i) := hhi i (Finset.mem_univ i)
  refine ⟨imin, imax, hl, hh, ?_⟩
  by_contra! h
  have heq (i) : v i = v imin := by linarith only [hl i, hh i, h]
  have hz : (n : ℝ) * v imin = 0 := by simpa [heq] using hzero
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hmin : v imin = 0 := (mul_eq_zero.mp hz).resolve_left hnne
  have hvzero : v = 0 := by ext i; exact (heq i).trans hmin
  rw [hvzero, norm_zero] at hunit
  norm_num at hunit

theorem plane_rounding {n : ℕ} (hn : 0 < n)
    (Y : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) (ε t : ℝ)
    (hε : 0 ≤ ε) (ht : 0 ≤ t) (hv : ‖v‖ = 1) (hvu : inner ℝ v (unitOnes n) = 0)
    (hnonneg : ∀ i j, 0 ≤ Y i j)
    (hclose : ‖Y - (Matrix.vecMulVec (unitOnes n) (unitOnes n) + Matrix.vecMulVec v v +
      ε • Matrix.of (fun (_ _ : Fin n) => (1 : ℝ)))‖ ≤ t) :
    ∃ S : Finset (Fin n), 0 < S.card ∧ S.card < n ∧
      ‖Y - blockMatrix S ε‖ ≤ t + 4 * n * Real.sqrt (ε + t) := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
  have hinv : (Real.sqrt (n : ℝ))⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hnpos))
  have hzero : ∑ i, v i = 0 := by
    rw [inner_unitOnes] at hvu
    exact (mul_eq_zero.mp hvu).resolve_right hinv
  have hunit : ∑ i, (v i) ^ 2 = 1 := by rw [← EuclideanSpace.real_norm_sq_eq, hv]; norm_num
  obtain ⟨imin, imax, hlo, hhi, hspread⟩ := extrema_strict hn v hzero hv
  let α := -v imin
  let β := v imax
  let S : Finset (Fin n) := Finset.univ.filter (fun i => v i + α ≤ β - v i)
  have hminS : imin ∈ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; dsimp [α, β]; linarith only [hspread]
  have hmaxS : imax ∉ S := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_le]; dsimp [α, β]; linarith only [hspread]
  have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨imin, hminS⟩
  have hSlt : S.card < n := by
    have hss : S ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, by
      intro he
      apply hmaxS
      rw [he]
      exact Finset.mem_univ _⟩
    simpa using Finset.card_lt_card hss
  let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => if i ∈ S then -α else β)
  have hwmin : w imin = -α := by simp [w, hminS]
  have hwmax : w imax = β := by simp [w, hmaxS]
  let u := unitOnes n
  let M := Matrix.vecMulVec u u + Matrix.vecMulVec v v +
    ε • Matrix.of (fun (_ _ : Fin n) => (1 : ℝ))
  have hpoint (i j) : |Y i j - ((n : ℝ)⁻¹ + v i * v j + ε)| ≤ t := by
    have h := (entry_le_frobenius (Y - M) i j).trans hclose
    simpa [M, u, unitOnes_outer hn, Matrix.vecMulVec_apply] using h
  have hround := nonnegative_endpoint_rounding hn v Y α β ε t imin imax hzero hunit
    (fun i => by dsimp [α]; linarith only [hlo i]) hhi
    (by simp [α]) rfl hnonneg hpoint
  have hroundsq : ‖v - w‖ ^ 2 ≤ n * (ε + t) := by
    simpa [EuclideanSpace.real_norm_sq_eq, w, S] using hround
  have hroundnorm : ‖v - w‖ ≤ n * Real.sqrt (ε + t) := by
    have hx : 0 ≤ ε + t := add_nonneg hε ht
    have hroot := Real.sq_sqrt hx
    have hbig : (n : ℝ) * (ε + t) ≤ (n : ℝ) ^ 2 * (ε + t) := by
      have hnlarge : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hn1]
      exact mul_le_mul_of_nonneg_right hnlarge hx
    have hrootsq := congrArg (fun a : ℝ => (n : ℝ) ^ 2 * a) hroot
    nlinarith only [hroundsq, hbig, hrootsq, norm_nonneg (v - w),
      mul_nonneg (le_of_lt hnpos) (Real.sqrt_nonneg (ε + t))]
  let z := w - inner ℝ u w • u
  have hu : ‖u‖ = 1 := unitOnes_norm hn
  have hz : z ≠ 0 := by
    intro he
    have h1 := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x imin) he
    have h2 := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x imax) he
    change w imin - inner ℝ u w * u imin = 0 at h1
    change w imax - inner ℝ u w * u imax = 0 at h2
    rw [hwmin] at h1
    rw [hwmax] at h2
    have huu : u imin = u imax := rfl
    rw [huu] at h1
    dsimp [α, β] at h1 h2
    linarith only [h1, h2, hspread]
  let v₀ := NormedSpace.normalize z
  have hv₀ : ‖v₀‖ = 1 := NormedSpace.norm_normalize_eq_one_iff.mpr hz
  have hzorth : inner ℝ z u = 0 := by
    dsimp [z]
    rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, hu, real_inner_comm u w]
    simp
  have hv₀orth : inner ℝ v₀ u = 0 := by
    simp [v₀, NormedSpace.normalize, inner_smul_left, hzorth]
  have hv₀zero : ∑ i, v₀ i = 0 := by
    rw [inner_unitOnes] at hv₀orth
    exact (mul_eq_zero.mp hv₀orth).resolve_right hinv
  let c := ‖z‖⁻¹ * (-α - inner ℝ u w * (Real.sqrt (n : ℝ))⁻¹)
  let d := ‖z‖⁻¹ * (β - inner ℝ u w * (Real.sqrt (n : ℝ))⁻¹)
  have hvalues (i) : v₀ i = if i ∈ S then c else d := by
    by_cases hi : i ∈ S <;>
      simp [v₀, NormedSpace.normalize, z, w, hi, c, d, u, unitOnes]
  have hblock := two_level_projector hn S hSpos hSlt v₀ c d ε hvalues hv₀zero hv₀
  have hcenter : ‖v - z‖ ≤ ‖v - w‖ := center_error u v w hu hvu
  have hnormalize : ‖v - v₀‖ ≤ 2 * ‖v - z‖ := normalize_error v z hv hz
  have houter := outer_difference_bound v v₀ hv hv₀
  have hdiff : M - blockMatrix S ε = Matrix.vecMulVec v v - Matrix.vecMulVec v₀ v₀ := by
    rw [← hblock]
    dsimp [M, u]
    abel
  refine ⟨S, hSpos, hSlt, ?_⟩
  have htri := norm_add_le (Y - M) (M - blockMatrix S ε)
  rw [sub_add_sub_cancel, hdiff] at htri
  change ‖Y - M‖ ≤ t at hclose
  linarith only [htri, hclose, houter, hnormalize, hcenter, hroundnorm]

theorem stability : StabilityClaim := by
  intro n ε η Y hn hε hεn hη hηone hgap hnonneg hrank herror
  have hnpos : 0 < n := by omega
  obtain ⟨v, hv, hvu, hclose⟩ :=
    near_optimal_plane hnpos Y ε η hε hεn hη hηone hgap hrank herror
  obtain ⟨S, hSpos, hSlt, hbound⟩ := plane_rounding hnpos Y v ε
    (3 * Real.sqrt (η / (ε * n))) (le_of_lt hε) (by positivity) hv hvu hnonneg hclose
  refine ⟨S, hSpos, hSlt, ?_⟩
  simpa only [frobenius_norm, stabilityBound] using hbound

end NMF

#print axioms NMF.endpoint_identity
#print axioms NMF.endpoint_distance
#print axioms NMF.endpoint_rounding

#print axioms NMF.nonnegative_endpoint_rounding

#print axioms NMF.normalize_error

#print axioms NMF.projection_error_split

#print axioms NMF.projection_base_residual

#print axioms NMF.projection_ones_trace

#print axioms NMF.projection_error_identity

#print axioms NMF.near_optimal_projection_bounds

#print axioms NMF.exists_column_projection

#print axioms NMF.rank_two_of_near_optimal

#print axioms NMF.stability
