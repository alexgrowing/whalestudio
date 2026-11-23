import Development.EtaleCohomology.EtaleSheaves.LeafGlueTwoPfFP

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Topology GlobalTheory.GlueModels LateralTheory.E.LeafGlueTwoPfFP

namespace LateralTheory.E.LeafGlueTwoPfQS

theorem qs_range {A D : Scheme.{0}} (e : A ⟶ D) [IsOpenImmersion e] [QuasiSeparatedSpace A] :
    IsQuasiSeparated (Set.range e) := by
  simpa [Set.image_univ] using (isQuasiSeparated_univ (α := A)).image_of_isEmbedding e.isOpenEmbedding.isEmbedding

theorem compact_pre {A D : Scheme.{0}} (e : A ⟶ D) [IsOpenImmersion e] {s : Set D} (hs : IsCompact s)
    (h : s ⊆ Set.range e) : IsCompact (e ⁻¹' s) :=
  (e.isOpenEmbedding.isInducing.isCompact_preimage_iff h).2 hs

theorem compact_inter_range {W A D : Scheme.{0}} (φ : W ⟶ A) (e : A ⟶ D) [IsOpenImmersion e] [QuasiCompact φ]
    {s : Set D} (hs : IsCompact s) (ho : IsOpen s) (h : s ⊆ Set.range e) :
    IsCompact (s ∩ Set.range (φ ≫ e)) := by
  rw [← Set.image_preimage_eq_inter_range]
  refine IsCompact.image ?_ (φ ≫ e).continuous
  have hp : ((φ ≫ e) ⁻¹' s) = φ ⁻¹' (e ⁻¹' s) := by ext x; simp
  rw [hp]
  exact QuasiCompact.isCompact_preimage (f := φ) _ (e.continuous.isOpen_preimage _ ho) (compact_pre e hs h)

set_option backward.isDefEq.respectTransparency false in
theorem leafPushoutQS : LeafPushoutQS := by
  intro DW DU DV φU φV _ _ hW hWs hUs hVs
  have := isOpenImmersion_inl φU φV
  have := isOpenImmersion_inr φU φV
  have : QuasiCompact φU := quasiCompact_of_compactSpace φU
  have : QuasiCompact φV := quasiCompact_of_compactSpace φV
  let good : Set (pushout φU φV : Scheme.{0}) → Prop := fun s => IsOpen s ∧ IsCompact s ∧
    (s ⊆ Set.range (pushout.inl φU φV) ∨ s ⊆ Set.range (pushout.inr φU φV))
  refine QuasiSeparatedSpace.of_isTopologicalBasis (b := fun s : {s // good s} => s.1) ?_ ?_
  · refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ ⟨s, rfl⟩; exact s.2.1
    · intro x u hx hu
      rcases pushout_cover φU φV x with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · have hb : ∀ {U : TopologicalSpace.Opens DU} {x : DU}, x ∈ U → ∃ U' ∈ DU.affineOpens, x ∈ U' ∧ U' ≤ U :=
          TopologicalSpace.Opens.isBasis_iff_nbhd.mp DU.isBasis_affineOpens
        obtain ⟨U', hU', hyU', hle⟩ := hb (U := ⟨pushout.inl φU φV ⁻¹' u, (pushout.inl φU φV).continuous.isOpen_preimage u hu⟩) (x := y) hx
        refine ⟨pushout.inl φU φV '' U', ⟨⟨_, (pushout.inl φU φV).isOpenEmbedding.isOpenMap _ U'.2,
          (show IsAffineOpen U' from hU').isCompact.image (pushout.inl φU φV).continuous, Or.inl (Set.image_subset_range _ _)⟩,
          rfl⟩, ⟨y, hyU', rfl⟩, Set.image_subset_iff.2 hle⟩
      · have hb : ∀ {U : TopologicalSpace.Opens DV} {x : DV}, x ∈ U → ∃ U' ∈ DV.affineOpens, x ∈ U' ∧ U' ≤ U :=
          TopologicalSpace.Opens.isBasis_iff_nbhd.mp DV.isBasis_affineOpens
        obtain ⟨U', hU', hyU', hle⟩ := hb (U := ⟨pushout.inr φU φV ⁻¹' u, (pushout.inr φU φV).continuous.isOpen_preimage u hu⟩) (x := y) hx
        refine ⟨pushout.inr φU φV '' U', ⟨⟨_, (pushout.inr φU φV).isOpenEmbedding.isOpenMap _ U'.2,
          (show IsAffineOpen U' from hU').isCompact.image (pushout.inr φU φV).continuous, Or.inr (Set.image_subset_range _ _)⟩,
          rfl⟩, ⟨y, hyU', rfl⟩, Set.image_subset_iff.2 hle⟩
  · have e : Set.range (φU ≫ pushout.inl φU φV) = Set.range (φV ≫ pushout.inr φU φV) := by
      rw [pushout.condition]
    have hWo : IsOpen (Set.range (φU ≫ pushout.inl φU φV)) := (φU ≫ pushout.inl φU φV).isOpenEmbedding.isOpen_range
    have mixed : ∀ s t : Set (pushout φU φV : Scheme.{0}), IsOpen s → IsCompact s →
        s ⊆ Set.range (pushout.inl φU φV) → IsOpen t → IsCompact t → t ⊆ Set.range (pushout.inr φU φV) →
        IsCompact (s ∩ t) := by
      intro s t so sc hs tO tc ht
      have hsub : s ∩ t ⊆ Set.range (φU ≫ pushout.inl φU φV) := by
        rintro x ⟨h1, h2⟩
        obtain ⟨a, rfl⟩ := hs h1
        obtain ⟨b, hb⟩ := ht h2
        obtain ⟨w, hw, -⟩ := exists_of_inl_eq_inr φU φV hb.symm
        exact ⟨w, by rw [Scheme.Hom.comp_apply, hw]⟩
      have hst : s ∩ t = (s ∩ Set.range (φU ≫ pushout.inl φU φV)) ∩ (t ∩ Set.range (φU ≫ pushout.inl φU φV)) := by
        ext x; constructor
        · intro hx; exact ⟨⟨hx.1, hsub hx⟩, ⟨hx.2, hsub hx⟩⟩
        · intro hx; exact ⟨hx.1.1, hx.2.1⟩
      rw [hst]
      refine qs_range (φU ≫ pushout.inl φU φV) _ _ Set.inter_subset_right (so.inter hWo)
        (compact_inter_range φU _ sc so hs) Set.inter_subset_right (tO.inter hWo) ?_
      rw [e]; exact compact_inter_range φV _ tc tO ht
    rintro ⟨s, so, sc, hs⟩ ⟨t, tO, tc, ht⟩
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact qs_range (pushout.inl φU φV) s t hs so sc ht tO tc
    · exact mixed s t so sc hs tO tc ht
    · show IsCompact (s ∩ t); rw [Set.inter_comm]; exact mixed t s tO tc ht so sc hs
    · exact qs_range (pushout.inr φU φV) s t hs so sc ht tO tc

theorem LeafGlueTwo_of : LateralTheory.E.LeafObjGluePf.LeafGlueTwo :=
  LateralTheory.E.LeafGlueTwoPfFP.LeafGlueTwo_of' leafPushoutQS

end LateralTheory.E.LeafGlueTwoPfQS
end
