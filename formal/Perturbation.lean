import Recovery

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.Frobenius

namespace NMF

noncomputable def matrixPairing {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

noncomputable def perturbedMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (ε δ : ℝ) : Matrix (Fin n) (Fin n) ℝ := baseMatrix n ε + δ • A

noncomputable def lossThreshold {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (δ d k g : ℝ) : ℝ :=
  n - 2 + 2 * δ * (Matrix.trace A - 2 * d + n * (k + g / 2)) + δ ^ 2 * frobeniusSq A

theorem rank_two_base_lower_bound {n : ℕ} (hn : 0 < n)
    (Y : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (hε : 0 ≤ ε) (hrank : Y.rank ≤ 2) :
    (n : ℝ) - 2 ≤ frobeniusSq (baseMatrix n ε - Y) := by
  obtain ⟨P, hsym, hidem, hfix, htrace⟩ := exists_column_projection Y
  rw [projection_error_identity hn Y P ε hsym hidem hfix, htrace]
  have hr : (Y.rank : ℝ) ≤ 2 := by exact_mod_cast hrank
  have ht : 0 ≤ (2 * ε * n + ε ^ 2 * (n : ℝ) ^ 2) *
      ((∑ i, (∑ j, (1 - P) i j) ^ 2) / n) := by positivity
  have he : 0 ≤ frobeniusSq (P * baseMatrix n ε - Y) := by unfold frobeniusSq; positivity
  linarith

theorem matrix_pairing_bound {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    matrixPairing A B ≤ ‖A‖ * ‖B‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin n × Fin n))
    (fun ij => A ij.1 ij.2) (fun ij => B ij.1 ij.2)
  simpa [Fintype.sum_prod_type, matrixPairing, ← frobenius_norm, frobeniusSq] using h

theorem perturbation_loss_identity {n : ℕ} (A Y : Matrix (Fin n) (Fin n) ℝ) (ε δ : ℝ) :
    frobeniusSq (perturbedMatrix A ε δ - Y) = frobeniusSq (baseMatrix n ε - Y) +
      2 * δ * matrixPairing A (baseMatrix n ε - Y) + δ ^ 2 * frobeniusSq A := by
  simp only [frobeniusSq, perturbedMatrix, matrixPairing, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem accepted_base_loss {n : ℕ} (hn : 3 ≤ n)
    (A Y : Matrix (Fin n) (Fin n) ℝ) (ε δ L d k g : ℝ)
    (hδ : 0 ≤ δ) (hL : 0 ≤ L) (hδL : δ * L ≤ 1)
    (hA : ‖A‖ ≤ L)
    (hbracket : Matrix.trace A - 2 * d + n * (k + g / 2) ≤ L)
    (haccepted : frobeniusSq (perturbedMatrix A ε δ - Y) ≤ lossThreshold A δ d k g) :
    frobeniusSq (baseMatrix n ε - Y) ≤ (n : ℝ) - 2 + 4 * n * δ * L := by
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ δ * L := mul_nonneg hδ hL
  have hAsq : frobeniusSq A ≤ L ^ 2 := by
    rw [frobeniusSq_norm]
    nlinarith [norm_nonneg A]
  have htau : lossThreshold A δ d k g ≤ (n : ℝ) - 2 + 2 * (δ * L) + (δ * L) ^ 2 := by
    unfold lossThreshold
    nlinarith only [mul_le_mul_of_nonneg_left hbracket (by positivity : 0 ≤ 2 * δ),
      mul_le_mul_of_nonneg_left hAsq (sq_nonneg δ)]
  have hnorm : ‖perturbedMatrix A ε δ - Y‖ ≤ n := by
    rw [frobeniusSq_norm] at haccepted
    nlinarith [sq_nonneg ((n : ℝ) - 2), norm_nonneg (perturbedMatrix A ε δ - Y),
      mul_self_le_mul_self hp hδL]
  have htriangle : ‖baseMatrix n ε - Y‖ ≤ ‖perturbedMatrix A ε δ - Y‖ + δ * L := by
    have heq : baseMatrix n ε - Y = (perturbedMatrix A ε δ - Y) - δ • A := by
      unfold perturbedMatrix
      abel
    rw [heq]
    calc
      _ ≤ ‖perturbedMatrix A ε δ - Y‖ + ‖δ • A‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ]; gcongr
  rw [frobeniusSq_norm]
  have hsquare := mul_self_le_mul_self (norm_nonneg (baseMatrix n ε - Y)) htriangle
  rw [frobeniusSq_norm] at haccepted
  have hcross := mul_le_mul_of_nonneg_right hnorm hp
  have hp2 : (δ * L) ^ 2 ≤ δ * L := by nlinarith
  have hlast : (4 : ℝ) * (δ * L) ≤ 2 * n * (δ * L) := by nlinarith
  nlinarith only [hsquare, haccepted, htau, hcross, hp2, hlast]

theorem perturbation_loss_lower {n : ℕ} (hn : 0 < n)
    (A Y Z : Matrix (Fin n) (Fin n) ℝ) (ε δ L r : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hrank : Y.rank ≤ 2) (hA : ‖A‖ ≤ L) (hclose : ‖Y - Z‖ ≤ r) :
    (n : ℝ) - 2 + 2 * δ * matrixPairing A (baseMatrix n ε - Z) +
      δ ^ 2 * frobeniusSq A - 2 * δ * L * r ≤ frobeniusSq (perturbedMatrix A ε δ - Y) := by
  have hlower := rank_two_base_lower_bound hn Y ε hε hrank
  have hbound := (matrix_pairing_bound A (Y - Z)).trans (mul_le_mul hA hclose (norm_nonneg _) hL)
  have hsplit : matrixPairing A (baseMatrix n ε - Y) =
      matrixPairing A (baseMatrix n ε - Z) - matrixPairing A (Y - Z) := by
    simp only [matrixPairing, Matrix.sub_apply, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [perturbation_loss_identity, hsplit]
  have hscaled := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 2 * δ)
  linarith


theorem chosen_parameter_bounds {n : ℕ} (hn : 3 ≤ n) (L g : ℝ)
    (hL : 1 ≤ L) (hg : 0 < g) (hg1 : g ≤ 1) :
    let r := g / (16 * L * n)
    let ε := r ^ 2 / (256 * (n : ℝ) ^ 2)
    let δ := ε ^ 3 / (144 * L)
    let η := 4 * n * δ * L
    0 < δ ∧ 0 < ε ∧ ε * n ≤ 1 ∧ δ * L ≤ 1 ∧
      0 < η ∧ η < 1 ∧ η < 2 * ε * n + ε ^ 2 * (n : ℝ) ^ 2 ∧
      stabilityBound n ε η < r ∧ r < 1 / (2 * n) ∧ 2 * L * r < n * g := by
  dsimp only
  let r := g / (16 * L * n)
  let ε := r ^ 2 / (256 * (n : ℝ) ^ 2)
  let δ := ε ^ 3 / (144 * L)
  let η := 4 * n * δ * L
  change 0 < δ ∧ 0 < ε ∧ ε * n ≤ 1 ∧ δ * L ≤ 1 ∧ 0 < η ∧ η < 1 ∧
    η < 2 * ε * n + ε ^ 2 * (n : ℝ) ^ 2 ∧ stabilityBound n ε η < r ∧
    r < 1 / (2 * n) ∧ 2 * L * r < n * g
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hLp : 0 < L := by linarith
  have hr : 0 < r := by dsimp [r]; positivity
  have hrn : r * n = g / (16 * L) := by dsimp [r]; field_simp
  have hrnsmall : r * n ≤ 1 / 16 := by
    rw [hrn]
    apply (div_le_iff₀ (by positivity : 0 < 16 * L)).mpr
    nlinarith only [hg1, hL]
  have hr1 : r ≤ 1 := by nlinarith only [hrnsmall, hnreal, hr]
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεeq : ε * (256 * (n : ℝ) ^ 2) = r ^ 2 := by
    dsimp [ε]
    field_simp
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hnreal]
  have hr2 : r ^ 2 ≤ r := by nlinarith only [hr, hr1]
  have hεr : ε < r := by nlinarith only [hεeq, hr2, hn2, hε]
  have hε1 : ε ≤ 1 := le_trans (le_of_lt hεr) hr1
  have hεn : ε * n ≤ 1 := by nlinarith only [hεr, hnpos, hrnsmall]
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ * L = ε ^ 3 / 144 := by dsimp [δ]; field_simp
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith only [hε, hε1]
  have hε3 : ε ^ 3 ≤ ε := by nlinarith only [mul_le_mul_of_nonneg_left hε2 (le_of_lt hε)]
  have hδL : δ * L ≤ 1 := by rw [hδeq]; linarith only [hε3, hε1]
  have hη : 0 < η := by dsimp [η]; positivity
  have hηeq : η = (ε ^ 2 * (ε * n)) / 36 := by dsimp [η]; rw [mul_assoc (4 * (n : ℝ)) δ L, hδeq]; ring
  have hηsmall : η ≤ 1 / 36 := by
    rw [hηeq]
    have h := mul_le_mul hε2 hεn (by positivity : 0 ≤ ε * n) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [h]
  have hηgap : η < 2 * ε * n + ε ^ 2 * (n : ℝ) ^ 2 := by
    have h : ε ^ 2 * (ε * n) ≤ ε * n := by nlinarith only [mul_le_mul_of_nonneg_right hε2 (by positivity : 0 ≤ ε * n)]
    rw [hηeq]
    have hp : 0 < ε * n := mul_pos hε hnpos
    have hs : 0 ≤ ε ^ 2 * (n : ℝ) ^ 2 := by positivity
    linarith only [h, hp, hs]
  have hrootε : Real.sqrt ε = r / (16 * n) := by
    apply (Real.sqrt_eq_iff_eq_sq (le_of_lt hε) (by positivity)).mpr
    dsimp [ε]
    field_simp
    ring
  have ht : 3 * Real.sqrt (η / (ε * n)) = ε / 2 := by
    have he : η / (ε * n) = (ε / 6) ^ 2 := by rw [hηeq]; field_simp; ring
    rw [he, Real.sqrt_sq (by positivity : 0 ≤ ε / 6)]
    ring
  have hroot : Real.sqrt (ε + ε / 2) ≤ 2 * Real.sqrt ε := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt (le_of_lt hε)]
      nlinarith only [hε]
  have hD : stabilityBound n ε η < r := by
    unfold stabilityBound
    rw [ht]
    have hb := mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ 4 * (n : ℝ))
    have hc : 4 * (n : ℝ) * (2 * Real.sqrt ε) = r / 2 := by rw [hrootε]; field_simp; ring
    rw [hc] at hb
    linarith only [hb, hεr]
  have hrthreshold : r < 1 / (2 * n) := by
    apply (lt_div_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mpr
    linarith only [hrnsmall]
  have hmargin : 2 * L * r < n * g := by
    have he : 2 * L * r = g / (8 * n) := by dsimp [r]; field_simp; ring
    rw [he]
    apply (div_lt_iff₀ (by positivity : 0 < 8 * (n : ℝ))).mpr
    nlinarith only [mul_pos hg (show 0 < 8 * (n : ℝ) ^ 2 - 1 by nlinarith only [hn2])]
  exact ⟨hδ, hε, hεn, hδL, hη, by linarith only [hηsmall], hηgap, hD, hrthreshold, hmargin⟩


theorem accepted_factor_rounding {n : ℕ} (hn : 3 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (L g d k : ℝ)
    (hL : 1 ≤ L) (hg : 0 < g) (hg1 : g ≤ 1) (hA : ‖A‖ ≤ L)
    (hbracket : Matrix.trace A - 2 * d + n * (k + g / 2) ≤ L)
    (W : Matrix (Fin n) (Fin 2) ℝ) (H : Matrix (Fin 2) (Fin n) ℝ)
    (hW : ∀ i j, 0 ≤ W i j) (hH : ∀ i j, 0 ≤ H i j) :
    let r := g / (16 * L * n)
    let ε := r ^ 2 / (256 * (n : ℝ) ^ 2)
    let δ := ε ^ 3 / (144 * L)
    frobeniusSq (perturbedMatrix A ε δ - W * H) ≤ lossThreshold A δ d k g →
      ∃ S : Finset (Fin n), 0 < S.card ∧ S.card < n ∧
        ‖W * H - blockMatrix S ε‖ < r ∧
        (∀ i j, ((W * H) i j > ε + 1 / (2 * n) ↔ sameBlock S i j)) := by
  dsimp only
  intro haccepted
  obtain ⟨hδ, hε, hεn, hδL, hη, hη1, hηgap, hD, hr, _⟩ :=
    chosen_parameter_bounds hn L g hL hg hg1
  have hnonneg : ∀ i j, 0 ≤ (W * H) i j := by
    intro i j
    simp only [Matrix.mul_apply]
    exact Finset.sum_nonneg (fun t _ => mul_nonneg (hW i t) (hH t j))
  have hrank : (W * H).rank ≤ 2 := (Matrix.rank_mul_le_left W H).trans W.rank_le_width
  have hbase := accepted_base_loss hn A (W * H) _ _ L d k g (le_of_lt hδ)
    (by linarith) hδL hA hbracket haccepted
  obtain ⟨S, hSp, hSn, hdist⟩ := stability n _ _ (W * H) hn hε hεn hη hη1 hηgap
    hnonneg hrank hbase
  refine ⟨S, hSp, hSn, ?_, ?_⟩
  · rw [← frobenius_norm]
    exact hdist.trans_lt hD
  · exact recover_same_block (by omega) (W * H) S hSp hSn _
      (hdist.trans_lt (hD.trans hr))

end NMF

#print axioms NMF.accepted_base_loss
#print axioms NMF.perturbation_loss_lower

#print axioms NMF.chosen_parameter_bounds

#print axioms NMF.accepted_factor_rounding
