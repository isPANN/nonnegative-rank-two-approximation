import ReductionSpec

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.Frobenius

namespace NMF.Reduction

theorem nonnegative_matrix_norm_le_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) : ‖A‖ ≤ ∑ i, ∑ j, A i j := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := (Finset.univ : Finset (Fin n × Fin n)))
    (f := fun ij => A ij.1 ij.2) (fun ij _ => hA ij.1 ij.2)
  simp only [Fintype.sum_prod_type] at h
  change frobeniusSq A ≤ (∑ i, ∑ j, A i j) ^ 2 at h
  rw [frobeniusSq_norm] at h
  have hs : 0 ≤ ∑ i, ∑ j, A i j := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hA i j))
  nlinarith only [h, norm_nonneg A, hs]

theorem nonnegative_trace_le_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) : Matrix.trace A ≤ ∑ i, ∑ j, A i j := by
  exact Finset.sum_le_sum (fun i _ => Finset.single_le_sum (fun j _ => hA i j) (Finset.mem_univ i))

theorem regularization_row_sum {n : ℕ} (C : Matrix (Fin n) (Fin n) ℕ) (d : ℕ)
    (hd : ∀ i, ∑ j, C i j ≤ d) (i : Fin n) :
    (∑ j, (C i j + if i = j then d - ∑ j, C i j else 0)) = d := by
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  exact Nat.add_sub_of_le (hd i)

theorem regularization_cut {n : ℕ} (C : Matrix (Fin n) (Fin n) ℕ) (d : ℕ)
    (S : Finset (Fin n)) :
    cutWeight (fun i j => ((C i j + if i = j then d - ∑ j, C i j else 0 : ℕ) : ℝ)) S =
      cutWeight (fun i j => (C i j : ℝ)) S := by
  classical
  unfold cutWeight
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i ≠ j := by intro heq; subst j; simp [hi] at hj
  simp [hij]

theorem integer_scale_bounds {n : ℕ} (hn : 3 ≤ n) (A : Matrix (Fin n) (Fin n) ℕ)
    (d cap : ℕ) (k : ℚ) (hk : 0 ≤ k) (hkc : k ≤ cap) :
    let L : ℕ := 1 + n + (∑ i, ∑ j, A i j) + 2 * d + n * (cap + 1)
    let g : ℝ := 1 / ((k.den : ℝ) * (n : ℝ) ^ 2)
    1 ≤ (L : ℝ) ∧ 0 < g ∧ g ≤ 1 ∧
      ‖(Matrix.of (fun i j => (A i j : ℝ)))‖ ≤ L ∧
      |Matrix.trace (Matrix.of (fun i j => (A i j : ℝ))) - 2 * d + n * ((k : ℝ) + g / 2)| ≤ L := by
  dsimp only
  let T : ℝ := ∑ i, ∑ j, (A i j : ℝ)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : (1 : ℝ) ≤ k.den := by exact_mod_cast k.den_pos
  have hg : 0 < 1 / ((k.den : ℝ) * (n : ℝ) ^ 2) := by positivity
  have hg1 : 1 / ((k.den : ℝ) * (n : ℝ) ^ 2) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hden, hnreal, mul_le_mul_of_nonneg_left hden (sq_nonneg (n : ℝ))]
  have hnorm := nonnegative_matrix_norm_le_sum (Matrix.of (fun i j => (A i j : ℝ))) (by intro i j; exact Nat.cast_nonneg (A i j))
  have htrace := nonnegative_trace_le_sum (Matrix.of (fun i j => (A i j : ℝ))) (by intro i j; exact Nat.cast_nonneg (A i j))
  dsimp only [Matrix.of_apply] at htrace
  have htrace0 : 0 ≤ Matrix.trace (Matrix.of (fun i j => (A i j : ℝ))) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
    positivity
  have hkr : 0 ≤ (k : ℝ) := by exact_mod_cast hk
  have hkcr : (k : ℝ) ≤ cap := by exact_mod_cast hkc
  have hterm : (n : ℝ) * ((k : ℝ) + (1 / ((k.den : ℝ) * (n : ℝ) ^ 2)) / 2) ≤ n * (cap + 1) := by
    gcongr
    linarith only [hkcr, hg1]
  have hterm0 : 0 ≤ (n : ℝ) * ((k : ℝ) + (1 / ((k.den : ℝ) * (n : ℝ) ^ 2)) / 2) := by positivity
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Nat.cast_sum]
  dsimp [T] at hT
  refine ⟨by linarith [mul_nonneg ((show (0 : ℝ) ≤ n by positivity)) (show (0 : ℝ) ≤ cap + 1 by positivity)], hg, hg1, ?_, ?_⟩
  · dsimp only [Matrix.of_apply] at hnorm
    linarith only [hnorm, hT, (show (0 : ℝ) ≤ d by positivity), (show (0 : ℝ) ≤ n by positivity), (show (0 : ℝ) ≤ cap by positivity),
      mul_nonneg ((show (0 : ℝ) ≤ n by positivity)) (show (0 : ℝ) ≤ cap + 1 by positivity)]
  · apply abs_le.mpr
    constructor <;> linarith only [htrace, htrace0, hterm, hterm0, hT,
      (show (0 : ℝ) ≤ d by positivity), (show (0 : ℝ) ≤ n by positivity), (show (0 : ℝ) ≤ cap by positivity),
      mul_nonneg ((show (0 : ℝ) ≤ n by positivity)) (show (0 : ℝ) ≤ cap + 1 by positivity)]


theorem cut_target_correct {n : ℕ} (hn : 3 ≤ n) (C : Matrix (Fin n) (Fin n) ℕ)
    (hsym : C.transpose = C) (k : ℚ) (hk : 0 ≤ k)
    (hkc : k ≤ (Finset.univ.sup (fun i => Finset.univ.sup (fun j => C i j)) : ℕ)) :
    (cutTarget C k).1.WellFormed ∧
    ((∃ S : Finset (Fin n), 0 < S.card ∧ S.card < n ∧
      cutDensity (fun i j => (C i j : ℝ)) S ≤ (k : ℝ)) ↔ (cutTarget C k).1.Feasible) ∧
    ∀ (W : Matrix (Fin n) (Fin 2) ℝ) (H : Matrix (Fin 2) (Fin n) ℝ),
      (cutTarget C k).1.ValidWitness W H →
      ∃ S : Finset (Fin n), 0 < S.card ∧ S.card < n ∧
        cutDensity (fun i j => (C i j : ℝ)) S ≤ (k : ℝ) ∧
        ∀ i j, ((W * H) i j > ((cutTarget C k).2 : ℝ) + 1 / (2 * n) ↔ sameBlock S i j) := by
  classical
  let d := Finset.univ.sup (fun i => ∑ j, C i j)
  let A : Matrix (Fin n) (Fin n) ℕ := fun i j => C i j + if i = j then d - ∑ j, C i j else 0
  let cap := Finset.univ.sup (fun i => Finset.univ.sup (fun j => C i j))
  let L : ℕ := 1 + n + (∑ i, ∑ j, A i j) + 2 * d + n * (cap + 1)
  let g : ℚ := 1 / ((k.den : ℚ) * (n : ℚ) ^ 2)
  let r : ℚ := g / (16 * L * n)
  let ε : ℚ := r ^ 2 / (256 * (n : ℚ) ^ 2)
  let δ : ℚ := ε ^ 3 / (144 * L)
  let R : Matrix (Fin n) (Fin n) ℝ := fun i j => (A i j : ℝ)
  have hgcast : (g : ℝ) = 1 / ((k.den : ℝ) * (n : ℝ) ^ 2) := by simp [g]
  have hrcast : (r : ℝ) = (g : ℝ) / (16 * L * n) := by simp [r]
  have hεcast : (ε : ℝ) = (r : ℝ) ^ 2 / (256 * (n : ℝ) ^ 2) := by simp [ε]
  have hδcast : (δ : ℝ) = (ε : ℝ) ^ 3 / (144 * L) := by simp [δ]
  obtain ⟨hL, hg, hg1, hnorm, hbracket⟩ := integer_scale_bounds hn A d cap k hk hkc
  change 1 ≤ (L : ℝ) at hL
  change ‖R‖ ≤ (L : ℝ) at hnorm
  rw [← hgcast] at hg hg1 hbracket
  change |Matrix.trace R - 2 * d + n * ((k : ℝ) + (g : ℝ) / 2)| ≤ (L : ℝ) at hbracket
  have hparams := chosen_parameter_bounds hn (L : ℝ) (g : ℝ) hL hg hg1
  dsimp only at hparams
  rw [← hrcast, ← hεcast, ← hδcast] at hparams
  obtain ⟨hδ, hε, _, _, _, hη1, _, _, _, _⟩ := hparams
  have hrows (i : Fin n) : (∑ j, R i j) = (d : ℝ) := by
    have hd (i : Fin n) : ∑ j, C i j ≤ d := Finset.le_sup (f := fun i => ∑ j, C i j) (Finset.mem_univ i)
    dsimp only [R, A]
    exact_mod_cast regularization_row_sum C d hd i
  have hRsym : R.transpose = R := by
    ext i j
    have hc : C j i = C i j := congrFun (congrFun hsym i) j
    by_cases hij : i = j
    · subst j; rfl
    · simp [R, A, Matrix.transpose_apply, hij, Ne.symm hij, hc]
  have hcut (S : Finset (Fin n)) : cutDensity R S = cutDensity (fun i j => (C i j : ℝ)) S := by
    unfold cutDensity
    rw [show cutWeight R S = _ from regularization_cut C d S]
  have hX : Matrix.of (fun i j => ((cutTarget C k).1.matrix i j : ℝ)) = perturbedMatrix R ε δ := by
    ext i j
    change (((if i = j then (1 : ℚ) else 0) + ε + δ * (A i j : ℚ) : ℚ) : ℝ) =
      (if i = j then 1 else 0) + (ε : ℝ) + (δ : ℝ) * R i j
    by_cases hij : i = j <;> simp [hij, R]
  have hτ : ((cutTarget C k).1.threshold : ℝ) = lossThreshold R δ d k g := by
    change (((n : ℚ) - 2 + 2 * δ * ((∑ i, (A i i : ℚ)) - 2 * d + n * (k + g / 2)) +
      δ ^ 2 * (∑ i, ∑ j, (A i j) ^ 2 : ℕ) : ℚ) : ℝ) = _
    simp [lossThreshold, frobeniusSq, Matrix.trace, Matrix.diag, R]
  have hvalid (W : Matrix (Fin n) (Fin 2) ℝ) (H : Matrix (Fin 2) (Fin n) ℝ) :
      (cutTarget C k).1.ValidWitness W H ↔ (∀ i j, 0 ≤ W i j) ∧ (∀ i j, 0 ≤ H i j) ∧
        frobeniusSq (perturbedMatrix R ε δ - W * H) ≤ lossThreshold R δ d k g := by
    unfold Target.ValidWitness
    rw [hX, hτ]
    rfl
  have hsnd : ((cutTarget C k).2 : ℝ) = (ε : ℝ) := rfl
  have hsound (W : Matrix (Fin n) (Fin 2) ℝ) (H : Matrix (Fin 2) (Fin n) ℝ)
      (hw : (cutTarget C k).1.ValidWitness W H) :
      ∃ S : Finset (Fin n), 0 < S.card ∧ S.card < n ∧
        cutDensity (fun i j => (C i j : ℝ)) S ≤ (k : ℝ) ∧
        ∀ i j, ((W * H) i j > ((cutTarget C k).2 : ℝ) + 1 / (2 * n) ↔ sameBlock S i j) := by
    obtain ⟨hW, hH, hloss⟩ := (hvalid W H).mp hw
    have h := accepted_cut_density hn R L g d k hL hg hg1 hnorm hRsym hrows
      (le_trans (le_abs_self _) hbracket)
      (fun S hSp hSn hgt => by
        rw [hgcast]
        exact integer_cut_density_gap A S hSp hSn k hgt) W H hW hH
    dsimp only at h
    rw [← hrcast, ← hεcast, ← hδcast] at h
    simpa only [hcut, hsnd] using h hloss
  refine ⟨?_, ⟨?_, ?_⟩, hsound⟩
  · refine ⟨by change 0 < n; omega, ?_, ?_⟩
    · intro i j
      have hentry : (0 : ℝ) ≤ perturbedMatrix R ε δ i j := by
        simp only [perturbedMatrix, baseMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, R]
        split_ifs <;> positivity
      have he := congrFun (congrFun hX i) j
      rw [← he] at hentry
      change (0 : ℝ) ≤ ((cutTarget C k).1.matrix i j : ℝ) at hentry
      exact_mod_cast hentry
    · have hbrlo := (abs_le.mp hbracket).1
      have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
      have hδL : 0 ≤ (δ : ℝ) * L := by positivity
      have hsmall : 2 * (δ : ℝ) * L < 1 := by
        nlinarith only [hη1, mul_nonneg (show (0 : ℝ) ≤ 4 * n - 2 by linarith) hδL]
      have hscaled := mul_le_mul_of_nonneg_left hbrlo (le_of_lt (mul_pos (by norm_num : (0 : ℝ) < 2) hδ))
      have hsquare : 0 ≤ (δ : ℝ) ^ 2 * frobeniusSq R := by unfold frobeniusSq; positivity
      have hτnonneg : 0 ≤ lossThreshold R δ d k g := by
        unfold lossThreshold
        nlinarith only [hnreal, hsmall, hscaled, hsquare]
      rw [← hτ] at hτnonneg
      exact_mod_cast hτnonneg
  · rintro ⟨S, hSp, hSn, hc⟩
    have hcR : cutDensity R S ≤ (k : ℝ) := by simpa only [hcut] using hc
    obtain ⟨W, H, hW, hH, hloss⟩ := cut_witness_feasible R S hSp hSn ε δ d k g
      (le_of_lt hε) (le_of_lt hδ) (le_of_lt hg) hRsym hrows hcR
    exact ⟨W, H, (hvalid W H).mpr ⟨hW, hH, hloss⟩⟩
  · rintro ⟨W, H, hw⟩
    obtain ⟨S, hSp, hSn, hc, _⟩ := hsound W H hw
    exact ⟨S, hSp, hSn, hc⟩

end NMF.Reduction

#print axioms NMF.Reduction.integer_scale_bounds

#print axioms NMF.Reduction.cut_target_correct
