import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology

private theorem card_sum_finset_swap {I : Type} (s : Finset I) (f : ℕ → I → Cardinal.{0}) :
    (Cardinal.sum fun q => ∑ i ∈ s, f q i) = ∑ i ∈ s, Cardinal.sum fun q => f q i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [Cardinal.sum_add_distrib', ih]

theorem UpperTheory.cohomology_part_bound_of_sum_bound :
    UpperTheory.V.Af.CohB.SumBound → UpperTheory.V.Af.CohB.PartSplit → UpperTheory.V.Af.CohB.PartBound := by
  intro h1 h2 Γ X I _ _ _ c hc d ξ
  obtain ⟨π, ι, h⟩ := h2 Γ X I c hc d ξ
  unfold UpperTheory.V.Af.CohB.totCoh
  rw [← card_sum_finset_swap]
  exact Cardinal.sum_le_sum _ _ fun q => h1 Γ I _ _ π ι h q
