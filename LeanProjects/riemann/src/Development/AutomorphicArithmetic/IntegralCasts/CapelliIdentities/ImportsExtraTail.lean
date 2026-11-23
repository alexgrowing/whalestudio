import Mathlib

theorem UpperTheory.Reformulated.B.Ydd5.main :
    ∀ {I : Type} (s : Finset I) (c : ℝ),
      (0 : ℝ) < c → ∀ (f : I → ℝ), (∀ (i : I), (0 : ℝ) < f i) → ∃ (ρ : ℝ), (0 : ℝ) < ρ ∧ ρ ≤ c ∧ ∀ i ∈ s, ρ ≤ f i := by
  intro I s c hc f hf
  classical
  refine Finset.induction_on s ?_ ?_
  · exact ⟨c, hc, le_rfl, by simp⟩
  · intro a t _ ih
    obtain ⟨ρ, h0, h1, h2⟩ := ih
    refine ⟨min ρ (f a), lt_min h0 (hf a), (min_le_left _ _).trans h1, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h2 i hi)
