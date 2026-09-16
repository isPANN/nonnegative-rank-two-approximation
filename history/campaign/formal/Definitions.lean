import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

set_option autoImplicit false

namespace NMF

noncomputable def frobeniusSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

noncomputable def baseMatrix (n : ℕ) (ε : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (if i = j then 1 else 0) + ε

noncomputable def blockMatrix {n : ℕ} (S : Finset (Fin n)) (ε : ℝ) :
    Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact fun i j => ε + if i ∈ S ∧ j ∈ S then (S.card : ℝ)⁻¹
    else if i ∉ S ∧ j ∉ S then ((n - S.card : ℕ) : ℝ)⁻¹ else 0

noncomputable def stabilityBound (n : ℕ) (ε η : ℝ) : ℝ :=
  let t := 3 * Real.sqrt (η / (ε * n))
  t + 4 * n * Real.sqrt (ε + t)

def StabilityClaim : Prop :=
  ∀ (n : ℕ) (ε η : ℝ) (Y : Matrix (Fin n) (Fin n) ℝ),
    3 ≤ n → 0 < ε → ε * n ≤ 1 → 0 < η → η < 1 →
    η < 2 * ε * n + ε ^ 2 * (n : ℝ) ^ 2 →
    (∀ i j, 0 ≤ Y i j) → Y.rank ≤ 2 →
    frobeniusSq (baseMatrix n ε - Y) ≤ (n : ℝ) - 2 + η →
    ∃ S : Finset (Fin n), 0 < S.card ∧ S.card < n ∧
      Real.sqrt (frobeniusSq (Y - blockMatrix S ε)) ≤ stabilityBound n ε η

end NMF
