import Perturbation

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.Frobenius

namespace NMF

noncomputable def cutWeight {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) : ℝ := ∑ i ∈ S, ∑ j ∈ Sᶜ, A i j

noncomputable def cutDensity {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) : ℝ := cutWeight A S / ((S.card : ℝ) * (n - S.card))

theorem block_pairing {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    matrixPairing A (blockMatrix S 0) =
      (S.card : ℝ)⁻¹ * (∑ i ∈ S, ∑ j ∈ S, A i j) +
      ((n - S.card : ℕ) : ℝ)⁻¹ * (∑ i ∈ Sᶜ, ∑ j ∈ Sᶜ, A i j) := by
  classical
  have hcompl : Finset.univ.filter (fun i => i ∉ S) = Sᶜ := by ext; simp
  have hrow (i : Fin n) : (∑ j, A i j * blockMatrix S 0 i j) =
      if i ∈ S then (S.card : ℝ)⁻¹ * ∑ j ∈ S, A i j
      else ((n - S.card : ℕ) : ℝ)⁻¹ * ∑ j ∈ Sᶜ, A i j := by
    by_cases hi : i ∈ S
    · simp [blockMatrix, hi, mul_ite, ← Finset.sum_mul, mul_comm]
    · simp [blockMatrix, hi, mul_ite, Finset.sum_ite, hcompl, ← Finset.sum_mul, mul_comm]
  unfold matrixPairing
  simp_rw [hrow]
  rw [Finset.sum_ite]
  simp [hcompl, ← Finset.mul_sum]

theorem block_pairing_cut {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (hSpos : 0 < S.card) (hSlt : S.card < n) (d : ℝ)
    (hsym : A.transpose = A) (hrow : ∀ i, ∑ j, A i j = d) :
    matrixPairing A (blockMatrix S 0) = 2 * d - n * cutDensity A S := by
  classical
  have hsymm (i j : Fin n) : A j i = A i j := congrFun (congrFun hsym i) j
  have hcross : (∑ i ∈ Sᶜ, ∑ j ∈ S, A i j) = cutWeight A S := by
    rw [Finset.sum_comm]
    simp_rw [hsymm]
    rfl
  have hs : (∑ i ∈ S, ∑ j ∈ S, A i j) + cutWeight A S = S.card * d := by
    rw [cutWeight, ← Finset.sum_add_distrib]
    simp_rw [Finset.sum_add_sum_compl, hrow]
    simp
  have ht : (∑ i ∈ Sᶜ, ∑ j ∈ Sᶜ, A i j) + cutWeight A S = (n - S.card : ℕ) * d := by
    rw [← hcross, ← Finset.sum_add_distrib]
    simp_rw [add_comm (∑ j ∈ Sᶜ, _) (∑ j ∈ S, _), Finset.sum_add_sum_compl, hrow]
    simp [Finset.card_compl]
  have ha : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hSpos)
  have hb : (n : ℝ) - S.card ≠ 0 := by
    have h : (S.card : ℝ) < n := by exact_mod_cast hSlt
    linarith
  have hcast : ((n - S.card : ℕ) : ℝ) = n - S.card := by
    exact_mod_cast Nat.cast_sub (le_of_lt hSlt)
  rw [block_pairing, hcast]
  rw [hcast] at ht
  have hss := eq_sub_of_add_eq hs
  have htt := eq_sub_of_add_eq ht
  rw [hss, htt, cutDensity]
  field_simp
  ring

theorem base_block_pairing {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) (ε : ℝ) :
    matrixPairing A (baseMatrix n ε - blockMatrix S ε) =
      Matrix.trace A - matrixPairing A (blockMatrix S 0) := by
  classical
  have heq : baseMatrix n ε - blockMatrix S ε = 1 - blockMatrix S 0 := by
    ext i j
    simp only [baseMatrix, blockMatrix, Matrix.sub_apply, Matrix.one_apply]
    ring
  rw [heq]
  simp [matrixPairing, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib,
    Matrix.one_apply, mul_ite, Matrix.trace, Matrix.diag]


theorem block_base_loss {n : ℕ} (S : Finset (Fin n))
    (hSpos : 0 < S.card) (hSlt : S.card < n) (ε : ℝ) :
    frobeniusSq (baseMatrix n ε - blockMatrix S ε) = (n : ℝ) - 2 := by
  classical
  have ha : (S.card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hSpos
  have hb : ((n - S.card : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt hSlt)
  have hcompl : Finset.univ.filter (fun i => i ∉ S) = Sᶜ := by ext; simp
  have hdiag : (∑ i, blockMatrix S 0 i i) = 2 := by
    simp only [blockMatrix, zero_add, and_self]
    have heq : (∑ i : Fin n, if i ∈ S then (S.card : ℝ)⁻¹ else
        if i ∉ S then ((n - S.card : ℕ) : ℝ)⁻¹ else 0) =
        ∑ i : Fin n, if i ∈ S then (S.card : ℝ)⁻¹ else ((n - S.card : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ S <;> simp [hi]
    rw [heq, sum_two_levels]
    field_simp
    norm_num
  have hsq : frobeniusSq (blockMatrix S 0) = 2 := by
    have hrow (i : Fin n) : (∑ j, (blockMatrix S 0 i j) ^ 2) = blockMatrix S 0 i i := by
      by_cases hi : i ∈ S
      · simp [blockMatrix, hi, ite_pow]
        field_simp
      · simp [blockMatrix, hi, ite_pow, Finset.sum_ite, hcompl, Finset.card_compl]
        field_simp
    simpa only [frobeniusSq, hrow] using hdiag
  have heq (i j : Fin n) : ((baseMatrix n ε - blockMatrix S ε) i j) ^ 2 =
      (if i = j then 1 else 0) - 2 * (if i = j then blockMatrix S 0 i j else 0) +
        (blockMatrix S 0 i j) ^ 2 := by
    simp only [Matrix.sub_apply, baseMatrix, blockMatrix, zero_add]
    by_cases hij : i = j <;> simp only [hij, ↓reduceIte] <;> ring
  unfold frobeniusSq
  simp_rw [heq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  change (n : ℝ) - 2 * (∑ i, blockMatrix S 0 i i) + frobeniusSq (blockMatrix S 0) = _
  rw [hdiag, hsq]
  ring

theorem block_perturbed_loss {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (hSpos : 0 < S.card) (hSlt : S.card < n) (d ε δ : ℝ)
    (hsym : A.transpose = A) (hrow : ∀ i, ∑ j, A i j = d) :
    frobeniusSq (perturbedMatrix A ε δ - blockMatrix S ε) =
      n - 2 + 2 * δ * (Matrix.trace A - 2 * d + n * cutDensity A S) + δ ^ 2 * frobeniusSq A := by
  rw [perturbation_loss_identity, block_base_loss S hSpos hSlt,
    base_block_pairing, block_pairing_cut A S hSpos hSlt d hsym hrow]
  ring

theorem block_has_nonnegative_factors {n : ℕ} (S : Finset (Fin n)) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ W : Matrix (Fin n) (Fin 2) ℝ, ∃ H : Matrix (Fin 2) (Fin n) ℝ,
      (∀ i j, 0 ≤ W i j) ∧ (∀ i j, 0 ≤ H i j) ∧ W * H = blockMatrix S ε := by
  classical
  let W : Matrix (Fin n) (Fin 2) ℝ := fun i j =>
    if j = 0 then (if i ∈ S then 1 else 0) else (if i ∉ S then 1 else 0)
  let H : Matrix (Fin 2) (Fin n) ℝ := fun i j => ε +
    if i = 0 then (if j ∈ S then (S.card : ℝ)⁻¹ else 0)
    else (if j ∉ S then ((n - S.card : ℕ) : ℝ)⁻¹ else 0)
  refine ⟨W, H, ?_, ?_, ?_⟩
  · intro i j
    dsimp [W]
    split_ifs <;> norm_num
  · intro i j
    dsimp [H]
    split_ifs <;> positivity
  · ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two, W, H]
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj, blockMatrix]


theorem integer_density_gap (w a b n q : ℕ) (p : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hq : 0 < q) (hab : a * b ≤ n ^ 2)
    (hgt : (p : ℝ) / q < (w : ℝ) / (a * b)) :
    (p : ℝ) / q + 1 / ((q : ℝ) * n ^ 2) ≤ (w : ℝ) / (a * b) := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have habr : (a : ℝ) * b ≤ (n : ℝ) ^ 2 := by exact_mod_cast hab
  have hcross : (p : ℝ) * (a * b) < (w : ℝ) * q := (div_lt_div_iff₀ hqr (mul_pos har hbr)).mp hgt
  have hint : (p : ℤ) * ((a : ℤ) * b) + 1 ≤ (w : ℤ) * q :=
    Int.add_one_le_iff.mpr (by exact_mod_cast hcross)
  have hreal : (p : ℝ) * (a * b) + 1 ≤ (w : ℝ) * q := by exact_mod_cast hint
  have hden : 0 < (q : ℝ) * (a * b) := by positivity
  have hden2 : 0 < (q : ℝ) * n ^ 2 := lt_of_lt_of_le hden (mul_le_mul_of_nonneg_left habr (le_of_lt hqr))
  have hfrac : 1 / ((q : ℝ) * n ^ 2) ≤ 1 / ((q : ℝ) * (a * b)) := by
    apply one_div_le_one_div_of_le hden
    exact mul_le_mul_of_nonneg_left habr (le_of_lt hqr)
  have hd : 1 / ((q : ℝ) * (a * b)) ≤ (w : ℝ) / (a * b) - (p : ℝ) / q := by
    apply (div_le_iff₀ hden).mpr
    field_simp
    nlinarith only [hreal]
  linarith only [hfrac, hd]

theorem accepted_cut_density {n : ℕ} (hn : 3 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (L g d k : ℝ)
    (hL : 1 ≤ L) (hg : 0 < g) (hg1 : g ≤ 1) (hA : ‖A‖ ≤ L)
    (hsym : A.transpose = A) (hrow : ∀ i, ∑ j, A i j = d)
    (hbracket : Matrix.trace A - 2 * d + n * (k + g / 2) ≤ L)
    (hgap : ∀ S : Finset (Fin n), 0 < S.card → S.card < n →
      k < cutDensity A S → k + g ≤ cutDensity A S)
    (W : Matrix (Fin n) (Fin 2) ℝ) (H : Matrix (Fin 2) (Fin n) ℝ)
    (hW : ∀ i j, 0 ≤ W i j) (hH : ∀ i j, 0 ≤ H i j) :
    let r := g / (16 * L * n)
    let ε := r ^ 2 / (256 * (n : ℝ) ^ 2)
    let δ := ε ^ 3 / (144 * L)
    frobeniusSq (perturbedMatrix A ε δ - W * H) ≤ lossThreshold A δ d k g →
      ∃ S : Finset (Fin n), 0 < S.card ∧ S.card < n ∧ cutDensity A S ≤ k ∧
        (∀ i j, ((W * H) i j > ε + 1 / (2 * n) ↔ sameBlock S i j)) := by
  dsimp only
  intro haccepted
  obtain ⟨hδ, hε, _, _, _, _, _, _, _, hmargin⟩ := chosen_parameter_bounds hn L g hL hg hg1
  obtain ⟨S, hSp, hSn, hdist, hrecover⟩ :=
    accepted_factor_rounding hn A L g d k hL hg hg1 hA hbracket W H hW hH haccepted
  refine ⟨S, hSp, hSn, ?_, hrecover⟩
  by_contra hcut
  have hgapS := hgap S hSp hSn (lt_of_not_ge hcut)
  have hlower := perturbation_loss_lower (by omega : 0 < n) A (W * H) (blockMatrix S _)
    _ _ L _ (le_of_lt hε) (le_of_lt hδ) (by linarith)
    ((Matrix.rank_mul_le_left W H).trans W.rank_le_width) hA (le_of_lt hdist)
  rw [base_block_pairing, block_pairing_cut A S hSp hSn d hsym hrow] at hlower
  unfold lossThreshold at haccepted
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hscaled := mul_le_mul_of_nonneg_left hgapS (le_of_lt (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hδ) hnpos))
  have hstrict := mul_lt_mul_of_pos_left hmargin hδ
  nlinarith only [hscaled, hstrict, hlower, haccepted]

theorem cut_witness_feasible {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) (hSp : 0 < S.card) (hSn : S.card < n) (ε δ d k g : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hg : 0 ≤ g)
    (hsym : A.transpose = A) (hrow : ∀ i, ∑ j, A i j = d) (hcut : cutDensity A S ≤ k) :
    ∃ W : Matrix (Fin n) (Fin 2) ℝ, ∃ H : Matrix (Fin 2) (Fin n) ℝ,
      (∀ i j, 0 ≤ W i j) ∧ (∀ i j, 0 ≤ H i j) ∧
      frobeniusSq (perturbedMatrix A ε δ - W * H) ≤ lossThreshold A δ d k g := by
  obtain ⟨W, H, hW, hH, hprod⟩ := block_has_nonnegative_factors S ε hε
  refine ⟨W, H, hW, hH, ?_⟩
  rw [hprod, block_perturbed_loss A S hSp hSn d ε δ hsym hrow]
  unfold lossThreshold
  have h := mul_le_mul_of_nonneg_left hcut (by positivity : 0 ≤ 2 * δ * (n : ℝ))
  have hgterm : 0 ≤ 2 * δ * (n : ℝ) * (g / 2) := by positivity
  nlinarith only [h, hgterm]


theorem integer_cut_density_gap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (S : Finset (Fin n)) (hSp : 0 < S.card) (hSn : S.card < n) (k : ℚ)
    (hgt : (k : ℝ) < cutDensity (fun i j => (A i j : ℝ)) S) :
    (k : ℝ) + 1 / ((k.den : ℝ) * n ^ 2) ≤ cutDensity (fun i j => (A i j : ℝ)) S := by
  classical
  have hcast : ((n - S.card : ℕ) : ℝ) = n - S.card := Nat.cast_sub (le_of_lt hSn)
  have hw : cutWeight (fun i j => (A i j : ℝ)) S = ((∑ i ∈ S, ∑ j ∈ Sᶜ, A i j : ℕ) : ℝ) := by
    simp [cutWeight]
  have hab : S.card * (n - S.card) ≤ n ^ 2 := by
    calc
      _ ≤ n * n := Nat.mul_le_mul (le_of_lt hSn) (Nat.sub_le _ _)
      _ = _ := (sq n).symm
  have hk : (k : ℝ) = (k.num : ℝ) / k.den := Rat.cast_def k
  simp only [cutDensity, hw, hk, ← hcast] at hgt ⊢
  exact integer_density_gap _ _ _ _ _ _ hSp (Nat.sub_pos_of_lt hSn) k.den_pos hab hgt


theorem identity_three_infeasible (W : Matrix (Fin 3) (Fin 2) ℝ)
    (H : Matrix (Fin 2) (Fin 3) ℝ) : ¬ frobeniusSq (1 - W * H) ≤ 0 := by
  have h := rank_two_base_lower_bound (by norm_num : 0 < 3) (W * H) 0 (by norm_num)
    ((Matrix.rank_mul_le_left W H).trans W.rank_le_width)
  have heq : baseMatrix 3 0 = 1 := by ext i j; simp [baseMatrix, Matrix.one_apply]
  rw [heq] at h
  norm_num at h
  linarith

theorem zero_target_feasible :
    frobeniusSq ((0 : Matrix (Fin 1) (Fin 1) ℝ) -
      (0 : Matrix (Fin 1) (Fin 2) ℝ) * (0 : Matrix (Fin 2) (Fin 1) ℝ)) ≤ 0 := by
  simp [frobeniusSq]

end NMF

#print axioms NMF.block_pairing_cut
#print axioms NMF.base_block_pairing

#print axioms NMF.block_perturbed_loss
#print axioms NMF.block_has_nonnegative_factors

#print axioms NMF.integer_density_gap
#print axioms NMF.accepted_cut_density
#print axioms NMF.cut_witness_feasible

#print axioms NMF.integer_cut_density_gap

#print axioms NMF.identity_three_infeasible
#print axioms NMF.zero_target_feasible
