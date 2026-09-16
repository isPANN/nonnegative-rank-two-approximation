import Reduction
import Lean

open NMF NMF.Reduction

def emit (s : Source) : IO Unit := do
  let t := forward s
  let input := Lean.Json.mkObj [
    ("variables", Lean.toJson (List.range s.numVars)),
    ("clauses", Lean.toJson (List.ofFn (fun j => (s.clauses j).map (fun l =>
      if l.2 then -((l.1.val + 1 : ℕ) : ℤ) else ((l.1.val + 1 : ℕ) : ℤ)))))]
  let output := Lean.Json.mkObj [
    ("X", Lean.toJson (List.ofFn (fun i => List.ofFn (fun j => toString (t.matrix i j))))),
    ("tau", Lean.toJson (toString t.threshold))]
  IO.println (Lean.Json.mkObj [("source", input), ("target", output)]).compress

def main : IO Unit := do
  emit ⟨0, 0, Fin.elim0, fun j => Fin.elim0 j⟩
  emit ⟨1, 1, fun _ => [], by intro j; simp⟩
  emit ⟨1, 1, fun _ => [(⟨0, by decide⟩, false)], by intro j; simp⟩
  emit ⟨1, 2, fun j => [(⟨0, by decide⟩, j.val == 1)], by intro j; simp⟩
  emit ⟨2, 1, fun _ => [(⟨0, by decide⟩, false), (⟨1, by decide⟩, true)], by intro j; simp⟩
  emit ⟨1, 1, fun _ => [(⟨0, by decide⟩, false), (⟨0, by decide⟩, true), (⟨0, by decide⟩, false)], by intro j; simp⟩
