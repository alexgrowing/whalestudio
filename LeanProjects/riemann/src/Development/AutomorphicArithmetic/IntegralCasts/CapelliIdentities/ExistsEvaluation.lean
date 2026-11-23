import Mathlib

theorem UpperTheory.Reformulated.B.ExistsEvaluation.exists_eval :
    ∀ {C Ω J : Type}
    [inst : CommRing C] [inst_1 : Field Ω] [Fintype J] (f : (J → C) →+* Ω),
    ∃ (j : J),
      ∀ (v : J → C), (f : (J → C) → Ω) v = (f : (J → C) → Ω) ((Algebra.algebraMap C (J → C) : C → J → C) (v j)) := by
  intro C Ω J _ _ _ f
  classical
  have hsum : ∑ j : J, f (Pi.single j 1) = 1 := by
    rw [← map_sum]
    have h : (∑ j : J, (Pi.single j (1 : C) : J → C)) = 1 := by
      simpa using Finset.univ_sum_single (1 : J → C)
    rw [h, map_one]
  obtain ⟨j, hj⟩ : ∃ j : J, f (Pi.single j 1) ≠ 0 := by
    by_contra hne
    push_neg at hne
    rw [Finset.sum_eq_zero (fun j _ => hne j)] at hsum
    exact zero_ne_one hsum
  have hidem : f (Pi.single j 1) * f (Pi.single j 1) = f (Pi.single j 1) := by
    rw [← map_mul]
    congr 1
    funext i
    by_cases hi : i = j
    · subst hi; simp
    · simp [Pi.single_eq_of_ne hi]
  have hone : f (Pi.single j 1) = 1 := by
    exact mul_left_cancel₀ hj (by rw [hidem, mul_one])
  refine ⟨j, fun v => ?_⟩
  have hmul : v * Pi.single j 1 =
      (Algebra.algebraMap C (J → C) : C → J → C) (v j) * Pi.single j 1 := by
    funext i
    by_cases hi : i = j
    · subst hi; simp [Algebra.algebraMap_eq_smul_one]
    · simp [Pi.single_eq_of_ne hi]
  have h2 := congrArg f hmul
  simpa [map_mul, hone] using h2
