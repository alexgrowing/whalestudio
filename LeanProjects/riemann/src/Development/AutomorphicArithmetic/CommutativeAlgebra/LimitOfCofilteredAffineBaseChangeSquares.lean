import Mathlib

open CategoryTheory Limits AlgebraicGeometry

private theorem exists_isCompact_preimage_eq_of_isLimit_of_isAffineHom {I : Type} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{0})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D) (hc : IsLimit c) (i0 : I)
    (W : c.pt.Opens) (hW : IsCompact (W : Set c.pt)) :
    ∃ (j : I) (_ : j ⟶ i0) (V : (D.obj j).Opens), IsCompact (V : Set (D.obj j)) ∧
      c.π.app j ⁻¹ᵁ V = W := by
  obtain ⟨Us, hsub, hfin, rfl⟩ :=
    (isBasis_preimage_isAffineOpen D c hc).exists_finite_of_isCompact hW
  clear hW
  induction Us, hfin using Set.Finite.induction_on with
  | empty => exact ⟨i0, 𝟙 i0, ⊥, by simp, by simp⟩
  | @insert U s hUs hs ih =>
    obtain ⟨i, V, hV, rfl⟩ := hsub (Set.mem_insert _ _)
    obtain ⟨j, fj, V', hV', e⟩ := ih (fun x hx => hsub (Set.mem_insert_of_mem _ hx))
    refine ⟨IsCofiltered.min i j, IsCofiltered.minToRight i j ≫ fj,
      D.map (IsCofiltered.minToLeft i j) ⁻¹ᵁ V ⊔ D.map (IsCofiltered.minToRight i j) ⁻¹ᵁ V', ?_, ?_⟩
    · rw [TopologicalSpace.Opens.coe_sup]
      exact (QuasiCompact.isCompact_preimage _ V.2 hV.isCompact).union
        (QuasiCompact.isCompact_preimage _ V'.2 hV')
    · rw [sSup_insert, ← e, Scheme.Hom.preimage_sup, ← Scheme.Hom.comp_preimage,
        ← Scheme.Hom.comp_preimage, c.w, c.w]

theorem UpperTheory.limit_of_cofiltered_affine_base_change_squares :
    ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (B DZ DY : I ⥤ Scheme.{0})
        [∀ {i j : I} (f : i ⟶ j), IsAffineHom (B.map f)]
        (α : DZ ⟶ DY) (pZ : DZ ⟶ B) (pY : DY ⟶ B), α ≫ pY = pZ →
        (∀ {i j : I} (f : i ⟶ j), IsPullback (DZ.map f) (pZ.app i) (pZ.app j) (B.map f)) →
        (∀ {i j : I} (f : i ⟶ j), IsPullback (DY.map f) (pY.app i) (pY.app j) (B.map f)) →
        ∀ (cZ : Cone DZ) (_ : IsLimit cZ) (cY : Cone DY) (_ : IsLimit cY),
        (∀ i, CompactSpace (DZ.obj i)) → (∀ i, QuasiSeparatedSpace (DZ.obj i)) →
        (∀ i, CompactSpace (DY.obj i)) → (∀ i, QuasiSeparatedSpace (DY.obj i)) →
        ∀ (i0 : I) (m : cZ.pt ⟶ cY.pt) [IsOpenImmersion m], (∀ i, cZ.π.app i ≫ α.app i = m ≫ cY.π.app i) →
        ∃ (j : I) (_ : j ⟶ i0) (V : (DY.obj j).Opens), IsCompact (V : Set (DY.obj j)) ∧
          α.app j ⁻¹ᵁ V = ⊤ ∧ cY.π.app j ⁻¹ᵁ V = m.opensRange := by
  intro I _ _ B DZ DY _ α pZ pY hα hZ hY cZ hcZ cY hcY hZc _ hYc _ i0 m _ hm
  have hZa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (DZ.map f) := fun f =>
    MorphismProperty.of_isPullback (P := @IsAffineHom) (hZ f).flip inferInstance
  have hYa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (DY.map f) := fun f =>
    MorphismProperty.of_isPullback (P := @IsAffineHom) (hY f).flip inferInstance
  haveI := Scheme.compactSpace_of_isLimit DZ cZ hcZ
  have hW : IsCompact (m.opensRange : Set cY.pt) := by
    rw [Scheme.Hom.coe_opensRange]
    exact isCompact_range m.continuous
  obtain ⟨j, fj, V, hV, e⟩ := exists_isCompact_preimage_eq_of_isLimit_of_isAffineHom DY cY hcY i0 m.opensRange hW
  have htop : cZ.π.app j ⁻¹ᵁ (α.app j ⁻¹ᵁ V) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, hm, Scheme.Hom.comp_preimage, e]
    exact Scheme.Hom.preimage_opensRange m
  obtain ⟨k, fkj, hk⟩ := exists_map_eq_top DZ cZ hcZ (α.app j ⁻¹ᵁ V) htop
  refine ⟨k, fkj ≫ fj, DY.map fkj ⁻¹ᵁ V, QuasiCompact.isCompact_preimage _ V.2 hV, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_preimage, ← α.naturality, Scheme.Hom.comp_preimage, hk]
  · rw [← Scheme.Hom.comp_preimage, cY.w, e]
