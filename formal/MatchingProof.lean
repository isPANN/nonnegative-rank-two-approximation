import ReductionSpec

set_option autoImplicit false
open scoped BigOperators

namespace NMF.Reduction

def sideSize {α : Type*} [Fintype α] (color : α → Bool) : ℕ :=
  ∑ i, if color i then 1 else 0

theorem side_sizes {α : Type*} [Fintype α] (color : α → Bool) :
    sideSize color + sideSize (fun i => !color i) = Fintype.card α := by
  unfold sideSize
  rw [← Finset.sum_add_distrib]
  have heq (i : α) : (if color i then 1 else 0) + (if !color i then 1 else 0) = 1 := by cases color i <;> rfl
  simp only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

theorem cut_constant {α : Type*} [Fintype α] (color : α → Bool) (M : ℕ) :
    directedCut (fun _ _ => M) color = M * sideSize color * sideSize (fun i => !color i) := by
  have heq (i j : α) : (if color i = true ∧ color j = false then M else 0) =
      M * (if color i then 1 else 0) * (if !color j then 1 else 0) := by
    by_cases hi : color i = true <;> by_cases hj : color j = true <;> simp_all
  simp only [directedCut, heq, sideSize, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem cut_transpose_flip {α : Type*} [Fintype α] (B : Matrix α α ℕ) (color : α → Bool) :
    directedCut B.transpose color = directedCut B (fun i => !color i) := by
  unfold directedCut
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.transpose_apply]
  by_cases hi : color i = true <;> by_cases hj : color j = true <;> simp_all

theorem cut_le_half_total {α : Type*} [Fintype α] (B : Matrix α α ℕ)
    (hsym : B.transpose = B) (color : α → Bool) :
    directedCut B color ≤ (∑ i, ∑ j, B i j) / 2 := by
  have hflip := cut_transpose_flip B color
  rw [hsym] at hflip
  have hsum : directedCut B color + directedCut B (fun i => !color i) ≤ ∑ i, ∑ j, B i j := by
    simp only [directedCut, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hi : color i = true <;> by_cases hj : color j = true <;> simp_all
  rw [← hflip] at hsum
  omega

theorem matching_weight_dominates {h : ℕ} (hh : 2 ≤ h) (B : Matrix (Fin h) (Fin h) ℕ) :
    (∑ i, ∑ j, B i j) < matchingWeight B := by
  let T := ∑ i, ∑ j, B i j
  have hT : T ≤ 2 * (T / 2) + 1 := by omega
  have hh2 : 6 ≤ h * (h + 1) := by nlinarith
  have hp := Nat.mul_le_mul_right (T / 2 + 1) hh2
  change T < h * (h + 1) * (T / 2 + 1)
  nlinarith only [hT, hp]

theorem matching_weight_entry_bound {h : ℕ} (hh : 2 ≤ h) (B : Matrix (Fin h) (Fin h) ℕ)
    (i j : Fin h) : B i j ≤ matchingWeight B := by
  have hj : B i j ≤ ∑ j, B i j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hi : (∑ j, B i j) ≤ ∑ i, ∑ j, B i j := Finset.single_le_sum (f := fun i => ∑ j, B i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact (hj.trans hi).trans (le_of_lt (matching_weight_dominates hh B))

theorem cut_complement {α : Type*} [Fintype α] [DecidableEq α]
    (B : Matrix α α ℕ) (M : ℕ) (hB : ∀ i j, B i j ≤ M) (color : α → Bool) :
    directedCut (fun i j => if i = j then 0 else M - B i j) color + directedCut B color =
      M * sideSize color * sideSize (fun i => !color i) := by
  rw [← cut_constant color M]
  simp only [directedCut, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j; cases color i <;> simp
  · cases color i <;> cases color j <;> simp [hij, Nat.sub_add_cancel (hB i j)]


def mateIndex {h : ℕ} (i : Fin h) (side : Bool) : Fin (2 * h) :=
  ⟨if side then h + i.val else i.val, by cases side <;> simp <;> omega⟩

def mateEquiv (h : ℕ) : Fin h × Bool ≃ Fin (2 * h) where
  toFun p := mateIndex p.1 p.2
  invFun i := if hi : i.val < h then (⟨i.val, hi⟩, false)
    else (⟨i.val - h, by omega⟩, true)
  left_inv p := by
    rcases p with ⟨i, side⟩
    cases side
    · simp [mateIndex, i.isLt]
    · have hh : ¬ h + i.val < h := by omega
      simp [mateIndex, hh]
  right_inv i := by
    by_cases hi : i.val < h
    · simp [hi, mateIndex]
    · simp [hi, mateIndex]
      apply Fin.ext
      simp
      omega

theorem sum_mateIndex {h : ℕ} (f : Fin (2 * h) → ℕ) :
    (∑ x, f x) = ∑ i : Fin h, (f (mateIndex i false) + f (mateIndex i true)) := by
  rw [← (mateEquiv h).sum_comp f]
  simp [Fintype.sum_prod_type, mateEquiv, add_comm]

def mateCount {h : ℕ} (color : Fin (2 * h) → Bool) : ℕ :=
  ∑ i : Fin h, if color (mateIndex i false) = color (mateIndex i true) then 0 else 1

theorem mate_count_bounds {h : ℕ} (color : Fin (2 * h) → Bool) :
    mateCount color ≤ sideSize color ∧ mateCount color ≤ sideSize (fun i => !color i) := by
  constructor <;> unfold mateCount sideSize <;> rw [sum_mateIndex] <;>
    apply Finset.sum_le_sum <;> intro i _ <;>
    by_cases hl : color (mateIndex i false) = true <;>
    by_cases hr : color (mateIndex i true) = true <;> simp_all

theorem mate_count_saturated {h : ℕ} (color : Fin (2 * h) → Bool)
    (hs : mateCount color = h) : ∀ i, color (mateIndex i true) = !color (mateIndex i false) := by
  have hb (i : Fin h) : (if color (mateIndex i false) = color (mateIndex i true) then 0 else 1 : ℕ) ≤ 1 := by
    split_ifs <;> omega
  have heq : (∑ i : Fin h, if color (mateIndex i false) = color (mateIndex i true) then 0 else 1 : ℕ) = ∑ _i : Fin h, 1 := by
    simpa [mateCount] using hs
  have he := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin h))) => hb i)).mp heq
  intro i
  have hi := he i (Finset.mem_univ i)
  by_cases hl : color (mateIndex i false) = true <;>
    by_cases hr : color (mateIndex i true) = true <;> simp_all


theorem matching_entries {h : ℕ} (B : Matrix (Fin h) (Fin h) ℕ) (i j : Fin h) :
    matchingMatrix B (mateIndex i false) (mateIndex j false) = B i j ∧
    matchingMatrix B (mateIndex i false) (mateIndex j true) = (if i = j then matchingWeight B else 0) ∧
    matchingMatrix B (mateIndex i true) (mateIndex j false) = (if i = j then matchingWeight B else 0) ∧
    matchingMatrix B (mateIndex i true) (mateIndex j true) = 0 := by
  have hi : ¬ h + i.val < h := by omega
  have hj : ¬ h + j.val < h := by omega
  have he : i.val ≠ h + j.val := by omega
  simp [matchingMatrix, mateIndex, i.isLt, j.isLt, hi, hj, he, Fin.ext_iff, eq_comm]

theorem matching_matrix_bound {h : ℕ} (hh : 2 ≤ h) (B : Matrix (Fin h) (Fin h) ℕ)
    (i j : Fin (2 * h)) : matchingMatrix B i j ≤ matchingWeight B := by
  unfold matchingMatrix
  split_ifs
  · exact matching_weight_entry_bound hh B _ _
  all_goals omega

theorem cross_diagonal_sum {h : ℕ} (l r : Fin h → Bool) (M : ℕ) :
    (∑ i, ∑ j, if l i = true ∧ r j = false then (if i = j then M else 0) else 0) =
      ∑ i, if l i = true ∧ r i = false then M else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

theorem matching_cut_identity {h : ℕ} (B : Matrix (Fin h) (Fin h) ℕ)
    (color : Fin (2 * h) → Bool) :
    directedCut (matchingMatrix B) color =
      directedCut B (fun i => color (mateIndex i false)) + matchingWeight B * mateCount color := by
  unfold directedCut
  rw [sum_mateIndex]
  simp_rw [sum_mateIndex, (matching_entries B _ _).1, (matching_entries B _ _).2.1,
    (matching_entries B _ _).2.2.1, (matching_entries B _ _).2.2.2]
  simp only [ite_self, add_zero, Finset.sum_add_distrib]
  rw [cross_diagonal_sum, cross_diagonal_sum]
  unfold mateCount
  simp only [Finset.mul_sum]
  have heq (i : Fin h) :
      (if color (mateIndex i false) = true ∧ color (mateIndex i true) = false then matchingWeight B else 0) +
      (if color (mateIndex i true) = true ∧ color (mateIndex i false) = false then matchingWeight B else 0) =
      matchingWeight B * (if color (mateIndex i false) = color (mateIndex i true) then 0 else 1) := by
    by_cases hl : color (mateIndex i false) = true <;>
      by_cases hr : color (mateIndex i true) = true <;> simp_all
  rw [add_assoc, ← Finset.sum_add_distrib]
  simp_rw [heq]


theorem directed_cut_partition {n : ℕ} (B : Matrix (Fin n) (Fin n) ℕ) (S : Finset (Fin n)) :
    directedCut B (fun i => decide (i ∈ S)) = ∑ i ∈ S, ∑ j ∈ Sᶜ, B i j := by
  classical
  have hcompl : Finset.univ.filter (fun i => i ∉ S) = Sᶜ := by ext; simp
  simp [directedCut, ite_and, Finset.sum_ite, hcompl]

theorem cast_directed_cut_partition {n : ℕ} (B : Matrix (Fin n) (Fin n) ℕ)
    (S : Finset (Fin n)) :
    (directedCut B (fun i => decide (i ∈ S)) : ℝ) = cutWeight (fun i j => (B i j : ℝ)) S := by
  classical
  simp [directed_cut_partition, cutWeight]

theorem complement_cut_sound {h : ℕ} (hh : 2 ≤ h) (B : Matrix (Fin h) (Fin h) ℕ)
    (hsym : B.transpose = B) (K : ℕ) (S : Finset (Fin (2 * h)))
    (hSp : 0 < S.card) (hSn : S.card < 2 * h)
    (hc : cutDensity (fun i j => (complementMatrix B i j : ℝ)) S ≤ (complementThreshold B K : ℝ)) :
    K ≤ directedCut B (fun i => decide (mateIndex i false ∈ S)) ∧
      ∀ i, decide (mateIndex i true ∈ S) = !decide (mateIndex i false ∈ S) := by
  classical
  let color : Fin (2 * h) → Bool := fun i => decide (i ∈ S)
  let a := S.card
  let b := 2 * h - S.card
  have ha : 0 < a := hSp
  have hb : 0 < b := Nat.sub_pos_of_lt hSn
  have hab : a + b = 2 * h := by dsimp [a, b]; omega
  have hsize : sideSize color = a := by simp [sideSize, color, a]
  have hsize' : sideSize (fun i => !color i) = b := by
    have hs := side_sizes color
    rw [hsize, Fintype.card_fin] at hs
    dsimp [a, b] at *
    omega
  have hcomp := cut_complement (matchingMatrix B) (matchingWeight B)
    (matching_matrix_bound hh B) color
  change directedCut (complementMatrix B) color + directedCut (matchingMatrix B) color = _ at hcomp
  rw [hsize, hsize', matching_cut_identity] at hcomp
  have hbcast : (b : ℝ) = 2 * h - (S.card : ℝ) := by
    dsimp [b]
    push_cast [Nat.cast_sub (le_of_lt hSn)]
    ring
  have hreal : (directedCut (complementMatrix B) color : ℝ) +
      ((directedCut B (fun i => color (mateIndex i false)) : ℝ) +
        matchingWeight B * (mateCount color : ℝ)) = matchingWeight B * ((a : ℝ) * b) := by
    exact_mod_cast (by simpa only [mul_assoc] using hcomp : directedCut (complementMatrix B) color +
      (directedCut B (fun i => color (mateIndex i false)) + matchingWeight B * mateCount color) = matchingWeight B * (a * b))
  have hden : (0 : ℝ) < a * b := by exact_mod_cast Nat.mul_pos ha hb
  have hcut : (directedCut (complementMatrix B) color : ℝ) / ((a : ℝ) * b) ≤
      (matchingWeight B : ℝ) - (matchingWeight B : ℝ) / h - (K : ℝ) / (h : ℝ) ^ 2 := by
    change cutWeight (fun i j => (complementMatrix B i j : ℝ)) S /
      ((S.card : ℝ) * ((2 * h : ℕ) - (S.card : ℝ))) ≤ _ at hc
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hc
    rw [← cast_directed_cut_partition, ← hbcast] at hc
    simpa [complementThreshold, a, color] using hc
  have haccepted : (matchingWeight B : ℝ) / h + (K : ℝ) / (h : ℝ) ^ 2 ≤
      ((matchingWeight B : ℝ) * mateCount color + directedCut B (fun i => color (mateIndex i false))) /
        ((a : ℝ) * b) := by
    have he : (directedCut (complementMatrix B) color : ℝ) / ((a : ℝ) * b) +
        ((matchingWeight B : ℝ) * mateCount color + directedCut B (fun i => color (mateIndex i false))) /
          ((a : ℝ) * b) = matchingWeight B := by
      rw [← add_div]
      apply (div_eq_iff (ne_of_gt hden)).mpr
      linarith only [hreal]
    linarith only [he, hcut]
  obtain ⟨hma, hmb⟩ := mate_count_bounds color
  rw [hsize] at hma
  rw [hsize'] at hmb
  obtain ⟨_, _, hmates, hK⟩ := matching_density_sound h a b (mateCount color)
    ((∑ i, ∑ j, B i j) / 2) (matchingWeight B)
    (directedCut B (fun i => color (mateIndex i false))) K (by omega) ha hb hab hma hmb
    (cut_le_half_total B hsym _) (chosen_matching_weight _ _ (by omega)) haccepted
  exact ⟨hK, mate_count_saturated color hmates⟩


def extendColor {h : ℕ} (color : Fin h → Bool) (i : Fin (2 * h)) : Bool :=
  let p := (mateEquiv h).symm i
  if p.2 then !color p.1 else color p.1

theorem extend_color_entries {h : ℕ} (color : Fin h → Bool) (i : Fin h) :
    extendColor color (mateIndex i false) = color i ∧
      extendColor color (mateIndex i true) = !color i := by
  have hi : ¬ h + i.val < h := by omega
  simp [extendColor, mateEquiv, mateIndex, i.isLt, hi]

theorem extended_cut_sizes {h : ℕ} (color : Fin h → Bool) :
    sideSize (extendColor color) = h ∧ mateCount (extendColor color) = h := by
  have he (i : Fin h) : (if color i then 1 else 0) + (if !color i then 1 else 0) = 1 := by
    cases color i <;> rfl
  constructor
  · unfold sideSize
    rw [sum_mateIndex]
    simp only [(extend_color_entries color _).1, (extend_color_entries color _).2, he]
    simp
  · unfold mateCount
    simp only [(extend_color_entries color _).1, (extend_color_entries color _).2]
    simp

theorem complement_cut_complete {h : ℕ} (hh : 2 ≤ h) (B : Matrix (Fin h) (Fin h) ℕ)
    (K : ℕ) (color : Fin h → Bool) (hcut : K ≤ directedCut B color) :
    ∃ S : Finset (Fin (2 * h)), 0 < S.card ∧ S.card < 2 * h ∧
      cutDensity (fun i j => (complementMatrix B i j : ℝ)) S ≤ (complementThreshold B K : ℝ) := by
  classical
  let S := Finset.univ.filter (fun i => extendColor color i = true)
  have hcolor : (fun i => decide (i ∈ S)) = extendColor color := by ext i; simp [S]
  have hcard : S.card = h := by
    have hc := (extended_cut_sizes color).1
    simpa [sideSize, S] using hc
  have hSp : 0 < S.card := by omega
  have hSn : S.card < 2 * h := by omega
  refine ⟨S, hSp, hSn, ?_⟩
  obtain ⟨hsize, hmates⟩ := extended_cut_sizes color
  have hsize' : sideSize (fun i => !(extendColor color i)) = h := by
    have hs := side_sizes (extendColor color)
    rw [hsize, Fintype.card_fin] at hs
    omega
  have hcomp := cut_complement (matchingMatrix B) (matchingWeight B)
    (matching_matrix_bound hh B) (extendColor color)
  change directedCut (complementMatrix B) (extendColor color) +
    directedCut (matchingMatrix B) (extendColor color) = _ at hcomp
  rw [hsize, hsize', matching_cut_identity, hmates] at hcomp
  simp only [(extend_color_entries color _).1] at hcomp
  have hweight : cutWeight (fun i j => (complementMatrix B i j : ℝ)) S =
      (directedCut (complementMatrix B) (extendColor color) : ℝ) := by
    rw [← cast_directed_cut_partition, hcolor]
  have hreal : (directedCut (complementMatrix B) (extendColor color) : ℝ) +
      ((directedCut B color : ℝ) + matchingWeight B * (h : ℝ)) =
        matchingWeight B * (h : ℝ) * h := by exact_mod_cast hcomp
  have hkr : (K : ℝ) ≤ directedCut B color := by exact_mod_cast hcut
  have hhpos : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  unfold cutDensity
  rw [hweight, hcard]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  have hden : (h : ℝ) * (2 * h - h) = (h : ℝ) ^ 2 := by ring
  rw [hden]
  simp only [complementThreshold, Rat.cast_sub, Rat.cast_natCast, Rat.cast_div, Rat.cast_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hhpos)).mpr
  field_simp
  nlinarith only [hreal, hkr]


theorem matching_matrix_symmetric {h : ℕ} (B : Matrix (Fin h) (Fin h) ℕ)
    (hsym : B.transpose = B) : (matchingMatrix B).transpose = matchingMatrix B := by
  ext i j
  obtain ⟨⟨a, x⟩, rfl⟩ := (mateEquiv h).surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := (mateEquiv h).surjective j
  change matchingMatrix B (mateIndex b y) (mateIndex a x) = matchingMatrix B (mateIndex a x) (mateIndex b y)
  have hB : B b a = B a b := congrFun (congrFun hsym a) b
  cases x <;> cases y <;>
    simp only [(matching_entries B _ _).1, (matching_entries B _ _).2.1,
      (matching_entries B _ _).2.2.1, (matching_entries B _ _).2.2.2, hB, eq_comm]

theorem complement_matrix_symmetric {h : ℕ} (B : Matrix (Fin h) (Fin h) ℕ)
    (hsym : B.transpose = B) : (complementMatrix B).transpose = complementMatrix B := by
  ext i j
  have hw := congrFun (congrFun (matching_matrix_symmetric B hsym) i) j
  change matchingMatrix B j i = matchingMatrix B i j at hw
  simp [complementMatrix, Matrix.transpose_apply, hw, eq_comm]

theorem complement_capacity {h : ℕ} (hh : 2 ≤ h) (B : Matrix (Fin h) (Fin h) ℕ) :
    matchingWeight B ≤ Finset.univ.sup (fun i => Finset.univ.sup (fun j => complementMatrix B i j)) := by
  let i : Fin h := ⟨0, by omega⟩
  let j : Fin h := ⟨1, by omega⟩
  have hij : mateIndex i true ≠ mateIndex j true := by
    intro he
    have hv := congrArg Fin.val he
    simp [mateIndex, i, j] at hv
  have he : complementMatrix B (mateIndex i true) (mateIndex j true) = matchingWeight B := by
    simp only [complementMatrix, if_neg hij, (matching_entries B i j).2.2.2, Nat.sub_zero]
  rw [← he]
  exact (Finset.le_sup (f := fun j => complementMatrix B (mateIndex i true) j) (Finset.mem_univ _)).trans
    (Finset.le_sup (f := fun i => Finset.univ.sup (fun j => complementMatrix B i j)) (Finset.mem_univ _))

theorem complement_threshold_bounds {h : ℕ} (hh : 2 ≤ h) (B : Matrix (Fin h) (Fin h) ℕ)
    (K : ℕ) (hK : K ≤ matchingWeight B) :
    0 ≤ complementThreshold B K ∧
      complementThreshold B K ≤ (Finset.univ.sup (fun i => Finset.univ.sup (fun j => complementMatrix B i j)) : ℕ) := by
  have hhq : (2 : ℚ) ≤ h := by exact_mod_cast hh
  have hhp : (0 : ℚ) < h := by linarith
  have hM : (0 : ℚ) ≤ matchingWeight B := by positivity
  have hKq : (K : ℚ) ≤ matchingWeight B := by exact_mod_cast hK
  have he : complementThreshold B K =
      ((matchingWeight B : ℚ) * (h : ℚ) ^ 2 - matchingWeight B * h - K) / (h : ℚ) ^ 2 := by
    unfold complementThreshold
    field_simp
  constructor
  · rw [he]
    apply div_nonneg _ (sq_nonneg _)
    have ht : (1 : ℚ) ≤ (h : ℚ) ^ 2 - h := by nlinarith only [hhq]
    have hm := mul_le_mul_of_nonneg_left ht hM
    nlinarith only [hm, hKq]
  · have hcap : (matchingWeight B : ℚ) ≤
        (Finset.univ.sup (fun i => Finset.univ.sup (fun j => complementMatrix B i j)) : ℕ) := by
      exact_mod_cast complement_capacity hh B
    unfold complementThreshold
    have h1 : (0 : ℚ) ≤ matchingWeight B / (h : ℚ) := by positivity
    have h2 : (0 : ℚ) ≤ K / (h : ℚ) ^ 2 := by positivity
    linarith only [hcap, h1, h2]

end NMF.Reduction

#print axioms NMF.Reduction.cut_complement
#print axioms NMF.Reduction.cut_le_half_total

#print axioms NMF.Reduction.mate_count_bounds
#print axioms NMF.Reduction.mate_count_saturated

#print axioms NMF.Reduction.matching_cut_identity

#print axioms NMF.Reduction.complement_cut_sound

#print axioms NMF.Reduction.complement_cut_complete

#print axioms NMF.Reduction.complement_threshold_bounds
