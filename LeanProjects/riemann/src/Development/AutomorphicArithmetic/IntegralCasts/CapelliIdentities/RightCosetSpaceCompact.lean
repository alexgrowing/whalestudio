import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.RightCosetSpaceCompact.RightCosetSpace.{u_1} :
    {G : Type u_1} → [inst : Group G] → Subgroup G → Type u_1 :=
    fun {G : Type u_1} [Group G] (Γ : Subgroup G) ↦ Quotient (MulAction.orbitRel (↥Γ) G)

noncomputable def UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk.{u_1} :
    {G : Type u_1} → [inst : Group G] → (Γ : Subgroup G) → G → UpperTheory.Reformulated.B.RightCosetSpaceCompact.RightCosetSpace Γ :=
    fun {G : Type u_1} [Group G] (Γ : Subgroup G) ↦ Quotient.mk (MulAction.orbitRel (↥Γ) G)

theorem UpperTheory.Reformulated.B.RightCosetSpaceCompact.exists_isCompact_subset_mk_image.{u_1} :
    ∀ {G : Type u_1} [inst : Group G] (Γ : Subgroup G) [inst_1 : TopologicalSpace G] [IsTopologicalGroup G]
      [LocallyCompactSpace G] {K : Set (UpperTheory.Reformulated.B.RightCosetSpaceCompact.RightCosetSpace Γ)},
      IsCompact K → ∃ (D : Set G), IsCompact D ∧ K ⊆ UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ '' D := by
  intro G _ Γ _ _ _ K hK
  have hopen : IsOpenMap (UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ) :=
    isOpenMap_quotient_mk'_mul (Γ := ↥Γ) (T := G)
  refine hK.induction_on
    (p := fun S => ∃ D : Set G, IsCompact D ∧ S ⊆ UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ '' D) ?_ ?_ ?_ ?_
  · exact ⟨∅, isCompact_empty, Set.empty_subset _⟩
  · rintro s t hst ⟨D, hD, htD⟩
    exact ⟨D, hD, hst.trans htD⟩
  · rintro s t ⟨D, hD, hsD⟩ ⟨E, hE, htE⟩
    refine ⟨D ∪ E, hD.union hE, ?_⟩
    rw [Set.image_union]
    exact Set.union_subset_union hsD htE
  · intro x _
    obtain ⟨g, rfl⟩ : ∃ g : G, UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ g = x := Quotient.exists_rep x
    obtain ⟨D, hD, hgD⟩ := exists_compact_mem_nhds g
    exact ⟨_, mem_nhdsWithin_of_mem_nhds (hopen.image_mem_nhds hgD), D, hD, subset_rfl⟩
