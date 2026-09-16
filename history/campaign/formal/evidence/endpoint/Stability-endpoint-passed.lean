import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open scoped BigOperators

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

end NMF

#print axioms NMF.endpoint_identity
#print axioms NMF.endpoint_distance
#print axioms NMF.endpoint_rounding

#print axioms NMF.nonnegative_endpoint_rounding
