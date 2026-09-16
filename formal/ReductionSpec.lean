import GraphReduction

set_option autoImplicit false
open scoped BigOperators

namespace NMF.Reduction

structure Source where
  numVars : ℕ
  clausesCount : ℕ
  clauses : Fin clausesCount → List (Literal numVars)
  arity : ∀ j, (clauses j).length ≤ 3

structure Target where
  size : ℕ
  matrix : Matrix (Fin size) (Fin size) ℚ
  threshold : ℚ

def Satisfiable (s : Source) : Prop := ∃ a, sourceWitness s.clauses a

def Target.WellFormed (t : Target) : Prop :=
  0 < t.size ∧ (∀ i j, 0 ≤ t.matrix i j) ∧ 0 ≤ t.threshold

def Target.ValidWitness (t : Target)
    (W : Matrix (Fin t.size) (Fin 2) ℝ) (H : Matrix (Fin 2) (Fin t.size) ℝ) : Prop :=
  (∀ i j, 0 ≤ W i j) ∧ (∀ i j, 0 ≤ H i j) ∧
    frobeniusSq (Matrix.of (fun i j => (t.matrix i j : ℝ)) - W * H) ≤ (t.threshold : ℝ)

def Target.Feasible (t : Target) : Prop :=
  ∃ W H, t.ValidWitness W H

def literalIndex {v : ℕ} (i : Fin (2 * v)) : Literal v :=
  (⟨i.val / 2, by omega⟩, i.val % 2 == 1)

def sourceGraph (s : Source) (hne : ∀ j, s.clauses j ≠ []) :
    Matrix (Fin (2 * (s.numVars + 1 + s.clausesCount)))
      (Fin (2 * (s.numVars + 1 + s.clausesCount))) ℕ :=
  let clauses := fun j : Fin s.clausesCount × Bool => naeClauses (padSource s.clauses hne) j.1 j.2
  fun i j => naeGraphMatrix clauses (literalIndex i) (literalIndex j)

def matchingWeight {h : ℕ} (B : Matrix (Fin h) (Fin h) ℕ) : ℕ :=
  h * (h + 1) * ((∑ i, ∑ j, B i j) / 2 + 1)

def matchingMatrix {h : ℕ} (B : Matrix (Fin h) (Fin h) ℕ) :
    Matrix (Fin (2 * h)) (Fin (2 * h)) ℕ :=
  fun i j => if hi : i.val < h then
    if hj : j.val < h then B ⟨i.val, hi⟩ ⟨j.val, hj⟩
    else if j.val = h + i.val then matchingWeight B else 0
  else if i.val = h + j.val then matchingWeight B else 0

def complementMatrix {h : ℕ} (B : Matrix (Fin h) (Fin h) ℕ) :
    Matrix (Fin (2 * h)) (Fin (2 * h)) ℕ :=
  fun i j => if i = j then 0 else matchingWeight B - matchingMatrix B i j

def complementThreshold {h : ℕ} (B : Matrix (Fin h) (Fin h) ℕ) (K : ℕ) : ℚ :=
  (matchingWeight B : ℚ) - (matchingWeight B : ℚ) / h - (K : ℚ) / (h : ℚ) ^ 2

def cutTarget {n : ℕ} (C : Matrix (Fin n) (Fin n) ℕ) (k : ℚ) : Target × ℚ :=
  let d := Finset.univ.sup (fun i => ∑ j, C i j)
  let A : Matrix (Fin n) (Fin n) ℕ := fun i j => C i j + if i = j then d - ∑ j, C i j else 0
  let cap := Finset.univ.sup (fun i => Finset.univ.sup (fun j => C i j))
  let L : ℕ := 1 + n + (∑ i, ∑ j, A i j) + 2 * d + n * (cap + 1)
  let g : ℚ := 1 / ((k.den : ℚ) * (n : ℚ) ^ 2)
  let r : ℚ := g / (16 * L * n)
  let ε : ℚ := r ^ 2 / (256 * (n : ℚ) ^ 2)
  let δ : ℚ := ε ^ 3 / (144 * L)
  let normSq : ℕ := ∑ i, ∑ j, (A i j) ^ 2
  let τ : ℚ := (n : ℚ) - 2 + 2 * δ * ((∑ i, (A i i : ℚ)) - 2 * d + n * (k + g / 2)) + δ ^ 2 * normSq
  (⟨n, fun i j => (if i = j then 1 else 0) + ε + δ * A i j, τ⟩, ε)

def construction (s : Source) : Target × ℚ :=
  if s.clausesCount = 0 then (⟨1, 0, 0⟩, 0)
  else if he : ∃ j, s.clauses j = [] then (⟨3, 1, 0⟩, 0)
  else
    let B := sourceGraph s (by intro j hj; exact he ⟨j, hj⟩)
    let K := naeGraphThreshold (s.numVars + 1 + s.clausesCount) (Fin s.clausesCount × Bool)
    cutTarget (complementMatrix B) (complementThreshold B K)

def forward (s : Source) : Target := (construction s).1

noncomputable def recover (s : Source)
    (W : Matrix (Fin (forward s).size) (Fin 2) ℝ)
    (H : Matrix (Fin 2) (Fin (forward s).size) ℝ) : Fin s.numVars → Bool := by
  classical
  exact if hs : s.clausesCount = 0 then fun _ => false
    else if he : ∃ j, s.clauses j = [] then fun _ => false
    else
      have hsize : (forward s).size = 2 * (2 * (s.numVars + 1 + s.clausesCount)) := by
        simp [forward, construction, hs, he, cutTarget]
      let first : Fin (forward s).size := ⟨0, by rw [hsize]; omega⟩
      let positive (i : Fin s.numVars) : Fin (forward s).size := ⟨2 * i.val, by rw [hsize]; omega⟩
      let reference : Fin (forward s).size := ⟨2 * s.numVars, by rw [hsize]; omega⟩
      let threshold : ℝ := ((construction s).2 : ℝ) + 1 / (2 * (forward s).size)
      fun i => decide ((W * H) first (positive i) > threshold) !=
        decide ((W * H) first reference > threshold)

def Correctness : Prop :=
  ∀ s : Source,
    (forward s).WellFormed ∧
    (Satisfiable s ↔ (forward s).Feasible) ∧
    ∀ (W : Matrix (Fin (forward s).size) (Fin 2) ℝ)
      (H : Matrix (Fin 2) (Fin (forward s).size) ℝ),
      (forward s).ValidWitness W H → sourceWitness s.clauses (recover s W H)

end NMF.Reduction
