import SourceGraphProof

set_option autoImplicit false

namespace NMF.Reduction

set_option backward.isDefEq.respectTransparency false in
theorem correctness : Correctness := by
  intro s
  by_cases hs : s.clausesCount = 0
  · have hsat (a : Fin s.numVars → Bool) : sourceWitness s.clauses a := by
      intro j
      have hj := j.isLt
      omega
    have hf : forward s = ⟨1, 0, 0⟩ := by simp [forward, construction, hs]
    have hwf : (forward s).WellFormed := by
      rw [hf]
      simp [Target.WellFormed]
    have hfeasible : (forward s).Feasible := by
      rw [hf]
      unfold Target.Feasible
      refine ⟨0, 0, ?_⟩
      simp [Target.ValidWitness, frobeniusSq, Matrix.of_apply]
    exact ⟨hwf, ⟨fun _ => hfeasible, fun _ => ⟨fun _ => false, hsat _⟩⟩,
      fun W H _ => hsat (recover s W H)⟩
  · by_cases he : ∃ j, s.clauses j = []
    · have hf : forward s = ⟨3, 1, 0⟩ := by simp [forward, construction, hs, he]
      have hwf : (forward s).WellFormed := by
        rw [hf]
        simp only [Target.WellFormed]
        refine ⟨by norm_num, ?_, by norm_num⟩
        intro i j
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      have hnosat : ¬ Satisfiable s := by
        obtain ⟨j, hj⟩ := he
        exact empty_clause_unsatisfiable s.clauses j hj
      have hnotarget : ¬ (forward s).Feasible := by
        rw [hf]
        unfold Target.Feasible
        rintro ⟨W, H, _, _, hloss⟩
        have hid : Matrix.of (fun i j => ((1 : Matrix (Fin 3) (Fin 3) ℚ) i j : ℝ)) =
            (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
          ext i j
          by_cases hij : i = j <;> simp [Matrix.of_apply, Matrix.one_apply, hij]
        simp only [Rat.cast_zero] at hloss
        change frobeniusSq (Matrix.of (fun i j => ((1 : Matrix (Fin 3) (Fin 3) ℚ) i j : ℝ)) - W * H) ≤ 0 at hloss
        rw [hid] at hloss
        exact identity_three_infeasible W H hloss
      exact ⟨hwf, ⟨fun h => (hnosat h).elim, fun h => (hnotarget h).elim⟩,
        fun W H hw => (hnotarget ⟨W, H, hw⟩).elim⟩
    · refine ⟨normal_forward_wellformed s hs he, ⟨normal_forward_complete s hs he, ?_⟩,
        normal_recovery s hs he⟩
      rintro ⟨W, H, hw⟩
      exact ⟨recover s W H, normal_recovery s hs he W H hw⟩

end NMF.Reduction

#print axioms NMF.Reduction.correctness
