import Stability

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.Frobenius

namespace NMF

def sameBlock {n : ℕ} (S : Finset (Fin n)) (i j : Fin n) : Prop :=
  (i ∈ S ↔ j ∈ S)

theorem block_entry_threshold {n : ℕ} (hn : 0 < n) (S : Finset (Fin n))
    (hSpos : 0 < S.card) (hSlt : S.card < n) (ε : ℝ) (i j : Fin n) :
    (sameBlock S i j → ε + (n : ℝ)⁻¹ ≤ blockMatrix S ε i j) ∧
    (¬ sameBlock S i j → blockMatrix S ε i j = ε) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : (0 : ℝ) < S.card := by exact_mod_cast hSpos
  have hb : (0 : ℝ) < (n - S.card : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hSlt
  have han : (S.card : ℝ) ≤ n := by exact_mod_cast (le_of_lt hSlt)
  have hbn : ((n - S.card : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n S.card
  have hia : (n : ℝ)⁻¹ ≤ (S.card : ℝ)⁻¹ := (inv_le_inv₀ hnpos ha).mpr han
  have hib : (n : ℝ)⁻¹ ≤ ((n - S.card : ℕ) : ℝ)⁻¹ := (inv_le_inv₀ hnpos hb).mpr hbn
  constructor
  · intro h
    by_cases hi : i ∈ S
    · have hj := h.mp hi
      simpa [blockMatrix, hi, hj] using add_le_add_left hia ε
    · have hj : j ∉ S := fun hmem => hi (h.mpr hmem)
      simpa [blockMatrix, hi, hj] using add_le_add_left hib ε
  · intro h
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      simp_all [sameBlock, blockMatrix]

theorem recover_same_block {n : ℕ} (hn : 0 < n)
    (Y : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (hSpos : 0 < S.card) (hSlt : S.card < n) (ε : ℝ)
    (hclose : Real.sqrt (frobeniusSq (Y - blockMatrix S ε)) < 1 / (2 * n))
    (i j : Fin n) :
    Y i j > ε + 1 / (2 * n) ↔ sameBlock S i j := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hi : (n : ℝ)⁻¹ = 2 * (1 / (2 * n)) := by field_simp
  have hentry := lt_of_le_of_lt (entry_le_frobenius (Y - blockMatrix S ε) i j)
    (by simpa only [frobenius_norm] using hclose)
  change |Y i j - blockMatrix S ε i j| < 1 / (2 * n) at hentry
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hentry
  obtain ⟨hsame, hdiff⟩ := block_entry_threshold hn S hSpos hSlt ε i j
  constructor
  · intro hy
    by_contra h
    rw [hdiff h] at hhi
    linarith only [hhi, hy]
  · intro h
    have hb := hsame h
    linarith only [hb, hlo, hi]

theorem stable_witness_recovery {n : ℕ} (hn : 3 ≤ n) (ε η : ℝ)
    (Y : Matrix (Fin n) (Fin n) ℝ)
    (hε : 0 < ε) (hεn : ε * n ≤ 1) (hη : 0 < η) (hηone : η < 1)
    (hgap : η < 2 * ε * n + ε ^ 2 * (n : ℝ) ^ 2)
    (hnonneg : ∀ i j, 0 ≤ Y i j) (hrank : Y.rank ≤ 2)
    (herror : frobeniusSq (baseMatrix n ε - Y) ≤ (n : ℝ) - 2 + η)
    (hsmall : stabilityBound n ε η < 1 / (2 * n)) :
    ∃ S : Finset (Fin n), 0 < S.card ∧ S.card < n ∧
      ∀ i j, (Y i j > ε + 1 / (2 * n) ↔ sameBlock S i j) := by
  obtain ⟨S, hSpos, hSlt, hdist⟩ := stability n ε η Y hn hε hεn hη hηone hgap
    hnonneg hrank herror
  refine ⟨S, hSpos, hSlt, ?_⟩
  exact recover_same_block (by omega) Y S hSpos hSlt ε (hdist.trans_lt hsmall)

end NMF

#print axioms NMF.stable_witness_recovery
