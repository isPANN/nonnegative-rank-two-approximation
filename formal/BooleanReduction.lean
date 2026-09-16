import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace NMF

abbrev Literal (n : ℕ) := Fin n × Bool
abbrev ThreeSAT (n m : ℕ) := Fin m → Fin 3 → Literal n

def literalValue {n : ℕ} (a : Fin n → Bool) (l : Literal n) : Bool := a l.1 ^^ l.2

def clauseValue (a b c : Bool) : Bool := a || b || c

def nae (a b c : Bool) : Bool := (a != b) || (b != c)

def chooseAuxiliary (a b c : Bool) : Bool := if a == b then !a else c

def satWitness {n m : ℕ} (s : ThreeSAT n m) (a : Fin n → Bool) : Prop :=
  ∀ j, clauseValue (literalValue a (s j 0)) (literalValue a (s j 1))
    (literalValue a (s j 2)) = true

def originalIndex {n m : ℕ} (i : Fin n) : Fin (n + 1 + m) := ⟨i, by omega⟩
def falseIndex (n m : ℕ) : Fin (n + 1 + m) := ⟨n, by omega⟩
def auxiliaryIndex {n m : ℕ} (j : Fin m) : Fin (n + 1 + m) := ⟨n + 1 + j, by omega⟩

def liftLiteral {n m : ℕ} (l : Literal n) : Literal (n + 1 + m) :=
  (originalIndex l.1, l.2)

def naeClauses {n m : ℕ} (s : ThreeSAT n m) (j : Fin m) (second : Bool) : Fin 3 → Literal (n + 1 + m) :=
  if second then ![(auxiliaryIndex j, true), liftLiteral (s j 2), (falseIndex n m, false)]
  else ![liftLiteral (s j 0), liftLiteral (s j 1), (auxiliaryIndex j, false)]

def naeWitness {n m : ℕ} (s : ThreeSAT n m) (b : Fin (n + 1 + m) → Bool) : Prop :=
  ∀ j second, nae (literalValue b (naeClauses s j second 0))
    (literalValue b (naeClauses s j second 1)) (literalValue b (naeClauses s j second 2)) = true

def extendAssignment {n m : ℕ} (s : ThreeSAT n m) (a : Fin n → Bool)
    (i : Fin (n + 1 + m)) : Bool :=
  if hi : i.val < n then a ⟨i.val, hi⟩ else
  if he : i.val = n then false else
    let j : Fin m := ⟨i.val - (n + 1), by omega⟩
    chooseAuxiliary (literalValue a (s j 0)) (literalValue a (s j 1))
      (literalValue a (s j 2))

def recoverAssignment {n m : ℕ} (b : Fin (n + 1 + m) → Bool) (i : Fin n) : Bool :=
  b (originalIndex i) ^^ b (falseIndex n m)

theorem nae_gadget_complete (a b c : Bool) (h : clauseValue a b c = true) :
    nae a b (chooseAuxiliary a b c) = true ∧
    nae (!(chooseAuxiliary a b c)) c false = true := by
  cases a <;> cases b <;> cases c <;> simp_all [clauseValue, nae, chooseAuxiliary]

theorem nae_gadget_sound (a b c f z : Bool)
    (h₁ : nae a b z = true) (h₂ : nae (!z) c f = true) :
    clauseValue (a ^^ f) (b ^^ f) (c ^^ f) = true := by
  cases a <;> cases b <;> cases c <;> cases f <;> cases z <;>
    simp_all [clauseValue, nae]

theorem extend_original {n m : ℕ} (s : ThreeSAT n m) (a : Fin n → Bool) (i : Fin n) :
    extendAssignment s a (originalIndex i) = a i := by
  simp [extendAssignment, originalIndex, i.isLt]

theorem extend_false {n m : ℕ} (s : ThreeSAT n m) (a : Fin n → Bool) :
    extendAssignment s a (falseIndex n m) = false := by simp [extendAssignment, falseIndex]

theorem extend_auxiliary {n m : ℕ} (s : ThreeSAT n m) (a : Fin n → Bool) (j : Fin m) :
    extendAssignment s a (auxiliaryIndex j) = chooseAuxiliary
      (literalValue a (s j 0)) (literalValue a (s j 1)) (literalValue a (s j 2)) := by
  have h₁ : ¬ n + 1 + j.val < n := by omega
  have h₂ : ¬ n + 1 + j.val = n := by omega
  simp [extendAssignment, auxiliaryIndex, h₁, h₂]

theorem extend_literal {n m : ℕ} (s : ThreeSAT n m) (a : Fin n → Bool) (l : Literal n) :
    literalValue (extendAssignment s a) (liftLiteral l) = literalValue a l := by
  simp [literalValue, liftLiteral, extend_original]

theorem recover_literal {n m : ℕ} (b : Fin (n + 1 + m) → Bool) (l : Literal n) :
    literalValue (recoverAssignment b) l = (literalValue b (liftLiteral l) ^^ b (falseIndex n m)) := by
  simp only [literalValue, recoverAssignment, liftLiteral]
  cases b (originalIndex l.1) <;> cases b (falseIndex n m) <;> cases l.2 <;> rfl

theorem sat_to_nae {n m : ℕ} (s : ThreeSAT n m) (a : Fin n → Bool)
    (h : satWitness s a) : naeWitness s (extendAssignment s a) := by
  intro j second
  have hg := nae_gadget_complete _ _ _ (h j)
  cases second
  · simpa [naeClauses, literalValue, liftLiteral, extend_original, extend_auxiliary, extend_false] using hg.1
  · simpa [naeClauses, literalValue, liftLiteral, extend_original, extend_auxiliary, extend_false] using hg.2

theorem nae_to_sat {n m : ℕ} (s : ThreeSAT n m) (b : Fin (n + 1 + m) → Bool)
    (h : naeWitness s b) : satWitness s (recoverAssignment b) := by
  intro j
  have h₁ := h j false
  have h₂ := h j true
  simp [naeClauses, literalValue] at h₁ h₂
  simp only [recover_literal]
  exact nae_gadget_sound _ _ _ _ _ h₁ h₂

theorem sat_iff_nae {n m : ℕ} (s : ThreeSAT n m) :
    (∃ a, satWitness s a) ↔ ∃ b, naeWitness s b :=
  ⟨fun ⟨a, ha⟩ => ⟨extendAssignment s a, sat_to_nae s a ha⟩,
   fun ⟨b, hb⟩ => ⟨recoverAssignment b, nae_to_sat s b hb⟩⟩


def padClause {n : ℕ} (c : List (Literal n)) (hne : c ≠ []) : Fin 3 → Literal n :=
  match c with
  | [] => False.elim (hne rfl)
  | [a] => ![a, a, a]
  | [a, b] => ![a, b, b]
  | a :: b :: c :: _ => ![a, b, c]

def sourceWitness {n m : ℕ} (s : Fin m → List (Literal n)) (a : Fin n → Bool) : Prop :=
  ∀ j, ∃ l ∈ s j, literalValue a l = true

def padSource {n m : ℕ} (s : Fin m → List (Literal n)) (hne : ∀ j, s j ≠ []) : ThreeSAT n m :=
  fun j => padClause (s j) (hne j)

theorem padding_preserves_clause {n : ℕ} (c : List (Literal n)) (hne : c ≠ [])
    (hlen : c.length ≤ 3) (a : Fin n → Bool) :
    (∃ l ∈ c, literalValue a l = true) ↔
      clauseValue (literalValue a (padClause c hne 0))
        (literalValue a (padClause c hne 1)) (literalValue a (padClause c hne 2)) = true := by
  match c with
  | [] => exact (hne rfl).elim
  | [x] => simp [padClause, clauseValue]
  | [x, y] => simp [padClause, clauseValue]
  | [x, y, z] => simp [padClause, clauseValue, or_assoc]
  | x :: y :: z :: w :: tail => simp at hlen

theorem padding_preserves_source {n m : ℕ} (s : Fin m → List (Literal n))
    (hne : ∀ j, s j ≠ []) (hlen : ∀ j, (s j).length ≤ 3) (a : Fin n → Bool) :
    sourceWitness s a ↔ satWitness (padSource s hne) a := by
  unfold sourceWitness satWitness padSource
  exact forall_congr' (fun j => padding_preserves_clause (s j) (hne j) (hlen j) a)

theorem empty_clause_unsatisfiable {n m : ℕ} (s : Fin m → List (Literal n))
    (j : Fin m) (h : s j = []) : ¬ ∃ a, sourceWitness s a := by
  rintro ⟨a, ha⟩
  simpa [h] using ha j

theorem empty_conjunction_satisfied {n : ℕ} (s : Fin 0 → List (Literal n)) :
    sourceWitness s (fun _ => false) := by intro j; exact Fin.elim0 j

end NMF

#print axioms NMF.sat_iff_nae
#print axioms NMF.nae_to_sat

#print axioms NMF.padding_preserves_source
#print axioms NMF.empty_clause_unsatisfiable
