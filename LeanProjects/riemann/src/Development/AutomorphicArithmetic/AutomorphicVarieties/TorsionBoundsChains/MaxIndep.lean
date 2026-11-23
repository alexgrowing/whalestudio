import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.maxIndep :
    ∀ (M : Type) [AddCommGroup M] [IsAddTorsionFree M] (s t : Set M), s ⊆ t →
      LinearIndepOn ℤ id s → ∃ b : Set M, s ⊆ b ∧ b ⊆ t ∧ LinearIndepOn ℤ id b ∧
        ∀ x ∈ t, ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ Submodule.span ℤ b := by
  intro M _ _ s t hst hs
  let S : Set (Set M) := {b | s ⊆ b ∧ b ⊆ t ∧ LinearIndepOn ℤ id b}
  obtain ⟨m, hsm, hmax⟩ := zorn_subset_nonempty S (by
    intro c hcS hc hne
    refine ⟨⋃₀ c, ⟨?_, ?_, ?_⟩, fun b hb => Set.subset_sUnion_of_mem hb⟩
    · obtain ⟨b, hb⟩ := hne
      exact (hcS hb).1.trans (Set.subset_sUnion_of_mem hb)
    · exact Set.sUnion_subset fun b hb => (hcS hb).2.1
    · exact linearIndepOn_sUnion_of_directed hc.directedOn fun b hb => (hcS hb).2.2)
    s ⟨subset_rfl, hst, hs⟩
  obtain ⟨-, hmt, hmi⟩ := hmax.prop
  refine ⟨m, hsm, hmt, hmi, fun x hx => ?_⟩
  by_cases hxm : x ∈ m
  · exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span hxm⟩
  have hdep : ¬ LinearIndepOn ℤ id (insert x m) := by
    intro hi
    have he := hmax.eq_of_subset
      ⟨hsm.trans (Set.subset_insert _ _), Set.insert_subset hx hmt, hi⟩ (Set.subset_insert _ _)
    exact hxm (he ▸ Set.mem_insert x m)
  rw [linearIndepOn_iff] at hdep
  push_neg at hdep
  obtain ⟨l, hl, hl0, hlne⟩ := hdep
  have hl' : Finsupp.erase x l ∈ Finsupp.supported ℤ ℤ m := by
    rw [Finsupp.mem_supported] at hl ⊢
    intro y hy
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hy
    have hyx : y ≠ x := by
      rintro rfl
      exact hy (by simp)
    rw [Finsupp.erase_ne hyx] at hy
    exact (hl (Finsupp.mem_support_iff.mpr hy)).resolve_left hyx
  have hsum : l x • x + Finsupp.linearCombination ℤ id (Finsupp.erase x l) = 0 := by
    have h1 := congrArg (Finsupp.linearCombination ℤ id) (Finsupp.single_add_erase x l)
    rw [map_add, Finsupp.linearCombination_single, hl0] at h1
    simpa using h1
  have hxne : l x ≠ 0 := by
    intro h0
    apply hlne
    have he : Finsupp.erase x l = l := by
      ext y
      by_cases hy : y = x
      · subst hy
        simp [h0]
      · simp [Finsupp.erase_ne hy]
    rw [← he]
    apply (linearIndepOn_iff.mp hmi) _ hl'
    rw [h0, zero_smul, zero_add] at hsum
    exact hsum
  refine ⟨l x, hxne, ?_⟩
  have hmem : Finsupp.linearCombination ℤ id (Finsupp.erase x l) ∈ Submodule.span ℤ m := by
    have h2 := (Finsupp.mem_span_image_iff_linearCombination ℤ (v := id) (s := m)).mpr ⟨_, hl', rfl⟩
    simpa using h2
  rw [eq_neg_of_add_eq_zero_left hsum]
  exact Submodule.neg_mem _ hmem
