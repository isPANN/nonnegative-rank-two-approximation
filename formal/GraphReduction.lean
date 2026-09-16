import BooleanReduction
import CutMatrix

set_option autoImplicit false
open scoped BigOperators

namespace NMF

def edgeCross {v : ℕ} (color : Literal v → Bool) (a b : Literal v) : ℕ :=
  if color a = color b then 0 else 1

def triangleCut {v : ℕ} (color : Literal v → Bool) (clause : Fin 3 → Literal v) : ℕ :=
  edgeCross color (clause 0) (clause 1) + edgeCross color (clause 1) (clause 2) +
    edgeCross color (clause 2) (clause 0)

def naeGraphScore {v : ℕ} {ι : Type*} [Fintype ι]
    (clauses : ι → Fin 3 → Literal v) (color : Literal v → Bool) : ℕ :=
  (∑ i : Fin v, (2 * Fintype.card ι + 1) * edgeCross color (i, false) (i, true)) +
    ∑ j, triangleCut color (clauses j)

def naeGraphThreshold (v : ℕ) (ι : Type*) [Fintype ι] : ℕ :=
  (2 * Fintype.card ι + 1) * v + 2 * Fintype.card ι

theorem triangle_cut_bound {v : ℕ} (color : Literal v → Bool) (clause : Fin 3 → Literal v) :
    triangleCut color clause ≤ 2 ∧
      (triangleCut color clause = 2 ↔ nae (color (clause 0)) (color (clause 1)) (color (clause 2)) = true) := by
  unfold triangleCut edgeCross nae
  cases color (clause 0) <;> cases color (clause 1) <;> cases color (clause 2) <;> decide

theorem nae_graph_saturation {v : ℕ} {ι : Type*} [Fintype ι]
    (clauses : ι → Fin 3 → Literal v) (color : Literal v → Bool)
    (h : naeGraphThreshold v ι ≤ naeGraphScore clauses color) :
    (∀ i, color (i, true) = !color (i, false)) ∧
      ∀ j, nae (color (clauses j 0)) (color (clauses j 1)) (color (clauses j 2)) = true := by
  have hp (i : Fin v) : (2 * Fintype.card ι + 1) * edgeCross color (i, false) (i, true) ≤
      2 * Fintype.card ι + 1 := by unfold edgeCross; split_ifs <;> omega
  have ht (j : ι) := (triangle_cut_bound color (clauses j)).1
  have hpsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin v))) => hp i)
  have htsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => ht j)
  have hpeq : (∑ i, (2 * Fintype.card ι + 1) * edgeCross color (i, false) (i, true)) =
      ∑ _i : Fin v, (2 * Fintype.card ι + 1) := by
    unfold naeGraphThreshold naeGraphScore at h
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hpsum htsum ⊢
    nlinarith only [h, hpsum, htsum]
  have hteq : (∑ j, triangleCut color (clauses j)) = ∑ _j : ι, 2 := by
    unfold naeGraphThreshold naeGraphScore at h
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hpeq htsum ⊢
    nlinarith only [h, hpeq, htsum]
  have hpair := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin v))) => hp i)).mp hpeq
  have htri := (Finset.sum_eq_sum_iff_of_le (fun j (_ : j ∈ (Finset.univ : Finset ι)) => ht j)).mp hteq
  constructor
  · intro i
    have he := hpair i (Finset.mem_univ i)
    unfold edgeCross at he
    cases hfalse : color (i, false) <;> cases htrue : color (i, true) <;> simp_all
  · intro j
    exact (triangle_cut_bound color (clauses j)).2.mp (htri j (Finset.mem_univ j))

theorem nae_graph_complete {v : ℕ} {ι : Type*} [Fintype ι]
    (clauses : ι → Fin 3 → Literal v) (a : Fin v → Bool)
    (h : ∀ j, nae (literalValue a (clauses j 0)) (literalValue a (clauses j 1))
      (literalValue a (clauses j 2)) = true) :
    naeGraphScore clauses (literalValue a) = naeGraphThreshold v ι := by
  have hp (i : Fin v) : edgeCross (literalValue a) (i, false) (i, true) = 1 := by
    simp [edgeCross, literalValue]
  have ht (j : ι) : triangleCut (literalValue a) (clauses j) = 2 :=
    (triangle_cut_bound (literalValue a) (clauses j)).2.mpr (h j)
  simp [naeGraphScore, naeGraphThreshold, hp, ht, mul_comm]

theorem nae_graph_sound {v : ℕ} {ι : Type*} [Fintype ι]
    (clauses : ι → Fin 3 → Literal v) (color : Literal v → Bool)
    (h : naeGraphThreshold v ι ≤ naeGraphScore clauses color) :
    ∀ j, nae (literalValue (fun i => color (i, false)) (clauses j 0))
      (literalValue (fun i => color (i, false)) (clauses j 1))
      (literalValue (fun i => color (i, false)) (clauses j 2)) = true := by
  obtain ⟨hp, ht⟩ := nae_graph_saturation clauses color h
  have he (l : Literal v) : literalValue (fun i => color (i, false)) l = color l := by
    rcases l with ⟨i, b⟩
    cases b <;> simp [literalValue, hp]
  simpa only [he] using ht

theorem sat_graph_sound {n m : ℕ} (s : ThreeSAT n m) (color : Literal (n + 1 + m) → Bool)
    (h : naeGraphThreshold (n + 1 + m) (Fin m × Bool) ≤
      naeGraphScore (fun j : Fin m × Bool => naeClauses s j.1 j.2) color) :
    satWitness s (recoverAssignment (fun i => color (i, false))) := by
  apply nae_to_sat
  intro j second
  exact nae_graph_sound (fun j : Fin m × Bool => naeClauses s j.1 j.2) color h (j, second)


theorem matching_density_sound (h a b matched E M x K : ℕ)
    (hh : 0 < h) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 2 * h)
    (hma : matched ≤ a) (hmb : matched ≤ b)
    (hx : x ≤ E) (hM : h * E < M)
    (haccepted : (M : ℝ) / h + (K : ℝ) / (h : ℝ) ^ 2 ≤
      (M * matched + x : ℝ) / (a * b)) :
    a = h ∧ b = h ∧ matched = h ∧ K ≤ x := by
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hdensity : (M : ℝ) / h ≤ (M * matched + x : ℝ) / (a * b) := by
    have hk : (0 : ℝ) ≤ K / (h : ℝ) ^ 2 := by positivity
    linarith only [haccepted, hk]
  have hcross : M * (a * b) ≤ (M * matched + x) * h := by
    have ht := (div_le_div_iff₀ hhr (mul_pos har hbr)).mp hdensity
    exact_mod_cast ht
  have exclude (a b : ℕ) (ha : 0 < a) (hlarge : h + 1 ≤ b)
      (hm : matched ≤ a) : (M * matched + x) * h < M * (a * b) := by
    have hp := Nat.mul_le_mul_left (M * h) hm
    have hq := Nat.mul_le_mul_right h hx
    have hr := Nat.mul_le_mul_left M (show 1 ≤ a by omega)
    have hs := Nat.mul_le_mul_left (M * a) hlarge
    nlinarith only [hp, hq, hr, hs, hM]
  have heqa : a = h := by
    by_contra hne
    by_cases hsmall : a < h
    · have ht := exclude a b ha (by omega) hma
      omega
    · have ht := exclude b a hb (by omega) hmb
      nlinarith only [ht, hcross]
  have heqb : b = h := by omega
  have heqm : matched = h := by
    by_contra hne
    have hm : matched + 1 ≤ h := by omega
    have hE : E < M := by nlinarith only [hM, Nat.mul_le_mul_right E hh]
    have hp := Nat.mul_le_mul_left M hm
    have hnum : M * matched + x < M * h := by nlinarith only [hp, hx, hE]
    rw [heqa, heqb] at hcross
    nlinarith only [hcross, Nat.mul_lt_mul_of_pos_right hnum hh]
  refine ⟨heqa, heqb, heqm, ?_⟩
  have heq : (M * h + x : ℝ) / ((h : ℝ) * h) = (M : ℝ) / h + (x : ℝ) / (h : ℝ) ^ 2 := by
    field_simp
  rw [heqa, heqb, heqm, heq] at haccepted
  have hk : (K : ℝ) / (h : ℝ) ^ 2 ≤ (x : ℝ) / (h : ℝ) ^ 2 := by linarith only [haccepted]
  have hh2 : (0 : ℝ) < (h : ℝ) ^ 2 := sq_pos_of_pos hhr
  exact_mod_cast (div_le_div_iff_of_pos_right hh2).mp hk

theorem chosen_matching_weight (h E : ℕ) (hh : 0 < h) :
    h * E < h * (h + 1) * (E + 1) := by
  have hp := Nat.mul_pos hh (Nat.succ_pos E)
  have hq := Nat.mul_le_mul_left h (show E < E + 1 by omega)
  nlinarith only [hh, hp, hq, Nat.mul_le_mul_left (h * (E + 1)) (show 1 ≤ h + 1 by omega)]


def directedCut {α : Type*} [Fintype α] (B : Matrix α α ℕ) (color : α → Bool) : ℕ :=
  ∑ i, ∑ j, if color i = true ∧ color j = false then B i j else 0

def undirectedEdge {α : Type*} [DecidableEq α] (a b : α) : Matrix α α ℕ :=
  if a = b then 0 else Matrix.single a b 1 + Matrix.single b a 1

theorem directed_cut_add {α : Type*} [Fintype α]
    (B C : Matrix α α ℕ) (color : α → Bool) :
    directedCut (B + C) color = directedCut B color + directedCut C color := by
  have heq (i j : α) : (if color i = true ∧ color j = false then B i j + C i j else 0) =
      (if color i = true ∧ color j = false then B i j else 0) +
      (if color i = true ∧ color j = false then C i j else 0) := by split_ifs <;> simp
  simp only [directedCut, Matrix.add_apply, heq, Finset.sum_add_distrib]

theorem directed_cut_single {α : Type*} [Fintype α] [DecidableEq α]
    (a b : α) (w : ℕ) (color : α → Bool) :
    directedCut (Matrix.single a b w) color = if color a = true ∧ color b = false then w else 0 := by
  classical
  unfold directedCut
  simp only [Matrix.single_apply]
  have heq (i j : α) : (if color i = true ∧ color j = false then
      (if a = i ∧ b = j then w else 0) else 0) =
      if a = i then if b = j then (if color a = true ∧ color b = false then w else 0) else 0 else 0 := by
    by_cases ha : a = i <;> by_cases hb : b = j <;> simp_all
  simp_rw [heq]
  simp

theorem directed_cut_edge {v : ℕ} (a b : Literal v) (color : Literal v → Bool) :
    directedCut (undirectedEdge a b) color = edgeCross color a b := by
  classical
  by_cases hab : a = b
  · subst b
    simp [undirectedEdge, directedCut, edgeCross]
  · rw [undirectedEdge, if_neg hab, directed_cut_add, directed_cut_single, directed_cut_single]
    unfold edgeCross
    cases color a <;> cases color b <;> decide


theorem directed_cut_sum {α ι : Type*} [Fintype α] [Fintype ι]
    (B : ι → Matrix α α ℕ) (color : α → Bool) :
    directedCut (∑ t, B t) color = ∑ t, directedCut (B t) color := by
  classical
  have heq (i j : α) : (if color i = true ∧ color j = false then ∑ t, B t i j else 0) =
      ∑ t, if color i = true ∧ color j = false then B t i j else 0 := by
    by_cases h : color i = true ∧ color j = false <;> simp [h]
  unfold directedCut
  simp only [Matrix.sum_apply, heq]
  calc
    _ = ∑ i, ∑ t, ∑ j, if color i = true ∧ color j = false then B t i j else 0 :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

theorem directed_cut_smul {α : Type*} [Fintype α]
    (B : Matrix α α ℕ) (c : ℕ) (color : α → Bool) :
    directedCut (c • B) color = c * directedCut B color := by
  simp only [directedCut, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_ite, mul_zero]

def naeGraphMatrix {v : ℕ} {ι : Type*} [Fintype ι]
    (clauses : ι → Fin 3 → Literal v) : Matrix (Literal v) (Literal v) ℕ :=
  (∑ i : Fin v, (2 * Fintype.card ι + 1) • undirectedEdge (i, false) (i, true)) +
    ∑ j, (undirectedEdge (clauses j 0) (clauses j 1) +
      undirectedEdge (clauses j 1) (clauses j 2) + undirectedEdge (clauses j 2) (clauses j 0))

theorem nae_graph_matrix_score {v : ℕ} {ι : Type*} [Fintype ι]
    (clauses : ι → Fin 3 → Literal v) (color : Literal v → Bool) :
    directedCut (naeGraphMatrix clauses) color = naeGraphScore clauses color := by
  simp only [naeGraphMatrix, directed_cut_add, directed_cut_sum, directed_cut_smul,
    directed_cut_edge, naeGraphScore, triangleCut]

theorem sat_graph_matrix_sound {n m : ℕ} (s : ThreeSAT n m)
    (color : Literal (n + 1 + m) → Bool)
    (h : naeGraphThreshold (n + 1 + m) (Fin m × Bool) ≤
      directedCut (naeGraphMatrix (fun j : Fin m × Bool => naeClauses s j.1 j.2)) color) :
    satWitness s (recoverAssignment (fun i => color (i, false))) := by
  apply sat_graph_sound s color
  simpa only [nae_graph_matrix_score] using h


theorem sat_graph_matrix_complete {n m : ℕ} (s : ThreeSAT n m) (a : Fin n → Bool)
    (ha : satWitness s a) :
    directedCut (naeGraphMatrix (fun j : Fin m × Bool => naeClauses s j.1 j.2))
      (literalValue (extendAssignment s a)) = naeGraphThreshold (n + 1 + m) (Fin m × Bool) := by
  rw [nae_graph_matrix_score]
  apply nae_graph_complete
  intro j
  exact sat_to_nae s a ha j.1 j.2

theorem padded_source_graph_equivalence {n m : ℕ} (s : Fin m → List (Literal n))
    (hne : ∀ j, s j ≠ []) (hlen : ∀ j, (s j).length ≤ 3) :
    (∃ a, sourceWitness s a) ↔
      ∃ color : Literal (n + 1 + m) → Bool,
        naeGraphThreshold (n + 1 + m) (Fin m × Bool) ≤
          directedCut (naeGraphMatrix (fun j : Fin m × Bool => naeClauses (padSource s hne) j.1 j.2)) color := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨literalValue (extendAssignment (padSource s hne) a), ?_⟩
    exact (sat_graph_matrix_complete (padSource s hne) a
      ((padding_preserves_source s hne hlen a).mp ha)).ge
  · rintro ⟨color, hc⟩
    refine ⟨recoverAssignment (fun i => color (i, false)), ?_⟩
    exact (padding_preserves_source s hne hlen _).mpr (sat_graph_matrix_sound _ color hc)

end NMF

#print axioms NMF.nae_graph_saturation
#print axioms NMF.nae_graph_complete
#print axioms NMF.sat_graph_sound

#print axioms NMF.matching_density_sound
#print axioms NMF.chosen_matching_weight

#print axioms NMF.directed_cut_edge

#print axioms NMF.sat_graph_matrix_sound

#print axioms NMF.padded_source_graph_equivalence
