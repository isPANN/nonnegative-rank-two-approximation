import MatchingProof
import ReductionProof

set_option autoImplicit false
open scoped BigOperators

namespace NMF.Reduction

def literalVertex {v : ℕ} (l : Literal v) : Fin (2 * v) :=
  ⟨2 * l.1.val + if l.2 then 1 else 0, by rcases l with ⟨i, b⟩; cases b <;> simp; omega⟩

def literalEquiv (v : ℕ) : Literal v ≃ Fin (2 * v) where
  toFun := literalVertex
  invFun := literalIndex
  left_inv l := by
    rcases l with ⟨i, b⟩
    apply Prod.ext
    · apply Fin.ext
      cases b <;> dsimp [literalIndex, literalVertex] <;> omega
    · cases b <;> simp [literalIndex, literalVertex, Nat.add_mod]
  right_inv i := by
    apply Fin.ext
    dsimp [literalIndex, literalVertex]
    have hm := Nat.mod_lt i.val (by decide : 0 < 2)
    have hd := Nat.mod_add_div i.val 2
    by_cases he : i.val % 2 = 1
    · simp [he]; omega
    · have hz : i.val % 2 = 0 := by omega
      simp [hz]; omega

theorem source_graph_cut (s : Source) (hne : ∀ j, s.clauses j ≠ [])
    (color : Fin (2 * (s.numVars + 1 + s.clausesCount)) → Bool) :
    directedCut (sourceGraph s hne) color =
      directedCut (naeGraphMatrix (fun j : Fin s.clausesCount × Bool =>
        naeClauses (padSource s.clauses hne) j.1 j.2)) (fun l => color (literalVertex l)) := by
  unfold directedCut
  rw [← (literalEquiv _).sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [← (literalEquiv _).sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  have hi := (literalEquiv _).symm_apply_apply i
  have hj := (literalEquiv _).symm_apply_apply j
  change literalIndex (literalVertex i) = i at hi
  change literalIndex (literalVertex j) = j at hj
  simp only [sourceGraph, literalEquiv, Equiv.coe_fn_mk, hi, hj]

theorem undirected_edge_symmetric {v : ℕ} (a b : Literal v) :
    (undirectedEdge a b).transpose = undirectedEdge a b := by
  by_cases hab : a = b
  · simp [undirectedEdge, hab]
  · simp [undirectedEdge, hab, Matrix.transpose_add, Matrix.transpose_single, add_comm]

theorem nae_graph_symmetric {v : ℕ} {ι : Type*} [Fintype ι]
    (clauses : ι → Fin 3 → Literal v) : (naeGraphMatrix clauses).transpose = naeGraphMatrix clauses := by
  simp only [naeGraphMatrix, Matrix.transpose_add, Matrix.transpose_sum, Matrix.transpose_smul,
    undirected_edge_symmetric]

theorem source_graph_symmetric (s : Source) (hne : ∀ j, s.clauses j ≠ []) :
    (sourceGraph s hne).transpose = sourceGraph s hne := by
  ext i j
  exact congrFun (congrFun (nae_graph_symmetric
    (fun j : Fin s.clausesCount × Bool => naeClauses (padSource s.clauses hne) j.1 j.2))
    (literalIndex i)) (literalIndex j)

theorem source_graph_complete (s : Source) (hne : ∀ j, s.clauses j ≠ [])
    (a : Fin s.numVars → Bool) (ha : sourceWitness s.clauses a) :
    ∃ color : Fin (2 * (s.numVars + 1 + s.clausesCount)) → Bool,
      naeGraphThreshold (s.numVars + 1 + s.clausesCount) (Fin s.clausesCount × Bool) ≤
        directedCut (sourceGraph s hne) color := by
  let b := extendAssignment (padSource s.clauses hne) a
  refine ⟨fun i => literalValue b (literalIndex i), ?_⟩
  rw [source_graph_cut]
  have he (l : Literal (s.numVars + 1 + s.clausesCount)) : literalIndex (literalVertex l) = l :=
    (literalEquiv _).symm_apply_apply l
  simp only [he]
  exact (sat_graph_matrix_complete (padSource s.clauses hne) a
    ((padding_preserves_source s.clauses hne s.arity a).mp ha)).ge

theorem sum_matrix_sum {α ι : Type*} [Fintype α] [Fintype ι]
    (B : ι → Matrix α α ℕ) : (∑ i, ∑ j, (∑ t, B t) i j) = ∑ t, ∑ i, ∑ j, B t i j := by
  simp only [Matrix.sum_apply]
  calc
    _ = ∑ i, ∑ t, ∑ j, B t i j := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

theorem undirected_edge_total {v : ℕ} (a b : Literal v) (hab : a ≠ b) :
    (∑ i, ∑ j, undirectedEdge a b i j) = 2 := by
  simp [undirectedEdge, hab, Matrix.add_apply, Finset.sum_add_distrib, Matrix.single_apply, ite_and]

theorem nae_graph_total_lower {v : ℕ} {ι : Type*} [Fintype ι]
    (clauses : ι → Fin 3 → Literal v) :
    2 * (2 * Fintype.card ι + 1) * v ≤ ∑ i, ∑ j, naeGraphMatrix clauses i j := by
  have hheavy : (∑ x, ∑ y, (∑ i : Fin v, (2 * Fintype.card ι + 1) • undirectedEdge (i, false) (i, true)) x y) =
      2 * (2 * Fintype.card ι + 1) * v := by
    rw [sum_matrix_sum]
    simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    simp [undirected_edge_total, mul_comm, mul_assoc]
  unfold naeGraphMatrix
  simp only [Matrix.add_apply, Finset.sum_add_distrib]
  rw [hheavy]
  omega

theorem source_graph_threshold_bound (s : Source) (hne : ∀ j, s.clauses j ≠ []) :
    naeGraphThreshold (s.numVars + 1 + s.clausesCount) (Fin s.clausesCount × Bool) ≤
      matchingWeight (sourceGraph s hne) := by
  let v := s.numVars + 1 + s.clausesCount
  let clauses := fun j : Fin s.clausesCount × Bool => naeClauses (padSource s.clauses hne) j.1 j.2
  have htotal : (∑ i, ∑ j, sourceGraph s hne i j) = ∑ i, ∑ j, naeGraphMatrix clauses i j := by
    rw [← (literalEquiv v).sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    rw [← (literalEquiv v).sum_comp]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg₂ (naeGraphMatrix clauses) ((literalEquiv v).symm_apply_apply i) ((literalEquiv v).symm_apply_apply j)
  have hlow := nae_graph_total_lower clauses
  change 2 * (2 * Fintype.card (Fin s.clausesCount × Bool) + 1) * v ≤ _ at hlow
  have hcap := matching_weight_dominates (show 2 ≤ 2 * v by dsimp [v]; omega) (sourceGraph s hne)
  rw [htotal] at hcap
  unfold naeGraphThreshold
  have hv : 1 ≤ v := by dsimp [v]; omega
  have hp := Nat.mul_le_mul_left (2 * Fintype.card (Fin s.clausesCount × Bool) + 1) hv
  change (2 * Fintype.card (Fin s.clausesCount × Bool) + 1) * v + 2 * Fintype.card (Fin s.clausesCount × Bool) ≤ _
  nlinarith only [hlow, hcap, hp]


theorem threshold_relative_membership {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) (threshold : ℝ)
    (h : ∀ i j, Y i j > threshold ↔ sameBlock S i j) (ref p q : Fin n) :
    (decide (Y ref p > threshold) != decide (Y ref q > threshold)) =
      (decide (p ∈ S) ^^ decide (q ∈ S)) := by
  classical
  simp only [h, sameBlock]
  by_cases hr : ref ∈ S <;> by_cases hp : p ∈ S <;> by_cases hq : q ∈ S <;> simp [hr, hp, hq]

theorem source_graph_sound (s : Source) (hne : ∀ j, s.clauses j ≠ [])
    (color : Fin (2 * (s.numVars + 1 + s.clausesCount)) → Bool)
    (hc : naeGraphThreshold (s.numVars + 1 + s.clausesCount) (Fin s.clausesCount × Bool) ≤
      directedCut (sourceGraph s hne) color) :
    sourceWitness s.clauses (recoverAssignment (fun i => color (literalVertex (i, false)))) := by
  rw [source_graph_cut] at hc
  exact (padding_preserves_source s.clauses hne s.arity _).mpr
    (sat_graph_matrix_sound (padSource s.clauses hne) (fun l => color (literalVertex l)) hc)

set_option backward.isDefEq.respectTransparency false in
theorem normal_recovery (s : Source) (hs : s.clausesCount ≠ 0)
    (he : ¬ ∃ j, s.clauses j = [])
    (W : Matrix (Fin (forward s).size) (Fin 2) ℝ)
    (H : Matrix (Fin 2) (Fin (forward s).size) ℝ)
    (hw : (forward s).ValidWitness W H) : sourceWitness s.clauses (recover s W H) := by
  let hne : ∀ j, s.clauses j ≠ [] := fun j hj => he ⟨j, hj⟩
  let B := sourceGraph s hne
  let K := naeGraphThreshold (s.numVars + 1 + s.clausesCount) (Fin s.clausesCount × Bool)
  let C := complementMatrix B
  let k := complementThreshold B K
  have hh : 2 ≤ 2 * (s.numVars + 1 + s.clausesCount) := by omega
  have hB : B.transpose = B := source_graph_symmetric s hne
  have hK : K ≤ matchingWeight B := source_graph_threshold_bound s hne
  obtain ⟨hk, hkcap⟩ := complement_threshold_bounds hh B K hK
  have hmain := cut_target_correct (by omega) C (complement_matrix_symmetric B hB) k hk hkcap
  have hconstruction : construction s = cutTarget C k := by simp [construction, hs, C, k, B, K, hne]
  have hforward : forward s = (cutTarget C k).1 := congrArg Prod.fst hconstruction
  have hsize := congrArg Target.size hforward
  let W' : Matrix (Fin (2 * (2 * (s.numVars + 1 + s.clausesCount)))) (Fin 2) ℝ :=
    fun i j => W ⟨i.val, by rw [hsize]; exact i.isLt⟩ j
  let H' : Matrix (Fin 2) (Fin (2 * (2 * (s.numVars + 1 + s.clausesCount)))) ℝ :=
    fun i j => H i ⟨j.val, by rw [hsize]; exact j.isLt⟩
  have hvalid : (cutTarget C k).1.ValidWitness W' H' := by
    have transfer (t : Target) (ht : forward s = t) :
        t.ValidWitness (fun i j => W (Fin.cast (congrArg Target.size ht).symm i) j)
          (fun i j => H i (Fin.cast (congrArg Target.size ht).symm j)) := by
      cases ht
      simpa using hw
    convert transfer _ hforward using 1 <;> funext i j <;> congr 1
  obtain ⟨S, hSp, hSn, hc, hround⟩ := hmain.2.2 W' H' hvalid
  have hcut := (complement_cut_sound hh B hB K S hSp hSn hc).1
  have hsat := source_graph_sound s hne (fun i => decide (mateIndex i false ∈ S)) hcut
  have heq : recover s W H = recoverAssignment (fun i => decide (mateIndex (literalVertex (i, false)) false ∈ S)) := by
    funext i
    let first : Fin (2 * (2 * (s.numVars + 1 + s.clausesCount))) := ⟨0, by omega⟩
    let positive : Fin (2 * (2 * (s.numVars + 1 + s.clausesCount))) := ⟨2 * i.val, by omega⟩
    let reference : Fin (2 * (2 * (s.numVars + 1 + s.clausesCount))) := ⟨2 * s.numVars, by omega⟩
    have hrelative := threshold_relative_membership (W' * H') S _ hround first positive reference
    have hthreshold : ((construction s).2 : ℝ) + 1 / (2 * (forward s).size) =
        ((cutTarget C k).2 : ℝ) + 1 / (2 * (2 * (2 * (s.numVars + 1 + s.clausesCount)))) := by
      rw [hconstruction, hsize]
      norm_cast
    simp only [recover, dif_neg hs, dif_neg he]
    rw [hthreshold]
    simpa only [W', H', Matrix.mul_apply, recoverAssignment, originalIndex, falseIndex,
      literalVertex, mateIndex, Bool.false_eq_true, ↓reduceIte, add_zero, first, positive, reference, Fin.cast_mk, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hrelative
  rw [heq]
  exact hsat

theorem normal_forward_complete (s : Source) (hs : s.clausesCount ≠ 0)
    (he : ¬ ∃ j, s.clauses j = []) (ha : Satisfiable s) : (forward s).Feasible := by
  let hne : ∀ j, s.clauses j ≠ [] := fun j hj => he ⟨j, hj⟩
  let B := sourceGraph s hne
  let K := naeGraphThreshold (s.numVars + 1 + s.clausesCount) (Fin s.clausesCount × Bool)
  obtain ⟨a, ha⟩ := ha
  obtain ⟨color, hc⟩ := source_graph_complete s hne a ha
  have hh : 2 ≤ 2 * (s.numVars + 1 + s.clausesCount) := by omega
  obtain ⟨S, hSp, hSn, hcut⟩ := complement_cut_complete hh B K color hc
  obtain ⟨hk, hkcap⟩ := complement_threshold_bounds hh B K (source_graph_threshold_bound s hne)
  have hmain := cut_target_correct (by omega) (complementMatrix B)
    (complement_matrix_symmetric B (source_graph_symmetric s hne)) (complementThreshold B K) hk hkcap
  simpa only [forward, construction, if_neg hs, dif_neg he] using hmain.2.1.mp ⟨S, hSp, hSn, hcut⟩

theorem normal_forward_wellformed (s : Source) (hs : s.clausesCount ≠ 0)
    (he : ¬ ∃ j, s.clauses j = []) : (forward s).WellFormed := by
  let hne : ∀ j, s.clauses j ≠ [] := fun j hj => he ⟨j, hj⟩
  let B := sourceGraph s hne
  let K := naeGraphThreshold (s.numVars + 1 + s.clausesCount) (Fin s.clausesCount × Bool)
  have hh : 2 ≤ 2 * (s.numVars + 1 + s.clausesCount) := by omega
  obtain ⟨hk, hkcap⟩ := complement_threshold_bounds hh B K (source_graph_threshold_bound s hne)
  have hmain := cut_target_correct (by omega) (complementMatrix B)
    (complement_matrix_symmetric B (source_graph_symmetric s hne)) (complementThreshold B K) hk hkcap
  simpa only [forward, construction, if_neg hs, dif_neg he] using hmain.1

end NMF.Reduction

#print axioms NMF.Reduction.source_graph_complete
#print axioms NMF.Reduction.source_graph_threshold_bound

#print axioms NMF.Reduction.normal_recovery
#print axioms NMF.Reduction.normal_forward_complete
#print axioms NMF.Reduction.normal_forward_wellformed
