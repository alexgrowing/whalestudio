import Formalism.PadicSubsetSums.StableGradedCounts.IRRExcludedCount

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem proposition_one_central_count : Prop1Core := by
  classical
  intro N Y P hN hY hP hcard
  have hb0 : (0 : ℝ) ≤ (3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) ((3 : ℝ) / 4)
    positivity
  have hne : P.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < P.card := lt_of_le_of_lt hb0 hcard
    exact_mod_cast this
  obtain ⟨g₁, hg₁⟩ := hne
  set S := P.filter (fun g => ¬ Disjoint (BB g₁ N) (BB g N)) with hSdef
  have hS := excluded_count_bound N g₁ Y S hN hY (hP g₁ hg₁).1 (by
    intro g hg
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hg
    exact ⟨(hP g h1).1, (hP g h1).2.1, (hP g h1).2.2, h2⟩)
  have hlt : S.card < P.card := by exact_mod_cast lt_of_le_of_lt hS hcard
  obtain ⟨g₂, hg₂, hn⟩ : ∃ g₂ ∈ P, g₂ ∉ S := by
    by_contra hcon
    push Not at hcon
    exact absurd (Finset.card_le_card (fun g hg => hcon g hg)) (not_le.mpr hlt)
  have hd : Disjoint (BB g₁ N) (BB g₂ N) := by
    by_contra h
    exact hn (Finset.mem_filter.mpr ⟨hg₂, h⟩)
  refine ⟨g₁, hg₁, g₂, hg₂, ?_, hd⟩
  rintro rfl
  have hmem : g₁ ∈ BB g₁ N := by simp [BB]
  exact Finset.disjoint_left.mp hd hmem hmem

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
