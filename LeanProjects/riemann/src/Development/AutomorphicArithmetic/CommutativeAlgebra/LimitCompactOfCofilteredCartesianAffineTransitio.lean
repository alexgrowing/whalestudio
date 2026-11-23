import Mathlib

open CategoryTheory Limits AlgebraicGeometry

private theorem core {J : Type} [SmallCategory J] [IsCofiltered J]
    (B DZ DY O : J ⥤ Scheme.{0}) (S0 Z0 Y0 : Scheme.{0})
    (pZ : DZ ⟶ B) (pY : DY ⟶ B) (α : DZ ⟶ DY) (ι : O ⟶ DY) (g : DZ ⟶ O)
    (hg : g ≫ ι = α) (hα : α ≫ pY = pZ) [∀ k, Mono (ι.app k)]
    (qB : B ⟶ (Functor.const J).obj S0) (qZ : DZ ⟶ (Functor.const J).obj Z0)
    (qY : DY ⟶ (Functor.const J).obj Y0)
    (pZ0 : Z0 ⟶ S0) (pY0 : Y0 ⟶ S0) (α0 : Z0 ⟶ Y0) (hα0 : α0 ≫ pY0 = pZ0)
    (hq : ∀ k, qZ.app k ≫ α0 = α.app k ≫ qY.app k)
    (hZ : ∀ k, IsPullback (qZ.app k) (pZ.app k) pZ0 (qB.app k))
    (hY : ∀ k, IsPullback (qY.app k) (pY.app k) pY0 (qB.app k))
    [LocallyOfFinitePresentation pZ0] [LocallyOfFiniteType pY0]
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (DZ.map f)]
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (O.map f)]
    [∀ k, CompactSpace (DZ.obj k)] [∀ k, CompactSpace (O.obj k)]
    [∀ k, QuasiSeparatedSpace (O.obj k)]
    (cO : Cone O) (hO : IsLimit cO) (cZ : Cone DZ) (hcZ : IsLimit cZ)
    (E : cO.pt ≅ cZ.pt) (hE : ∀ k, E.hom ≫ cZ.π.app k ≫ g.app k = cO.π.app k)
    (a : cZ.pt ⟶ Z0) (ha : ∀ k, cZ.π.app k ≫ qZ.app k = a) :
    ∃ k, IsIso (g.app k) := by
  let tO : O ⟶ (Functor.const J).obj S0 := ι ≫ qY ≫ (Functor.const J).map pY0
  let tZ : DZ ⟶ (Functor.const J).obj S0 := qZ ≫ (Functor.const J).map pZ0
  have htO : ∀ k, tO.app k = ι.app k ≫ qY.app k ≫ pY0 := fun k => rfl
  have htZ : ∀ k, tZ.app k = qZ.app k ≫ pZ0 := fun k => rfl
  have hgk : ∀ k, g.app k ≫ ι.app k = α.app k := fun k => by
    simpa using congr_app hg k
  have hαk : ∀ k, α.app k ≫ pY.app k = pZ.app k := fun k => by
    simpa using congr_app hα k
  have hcZg : ∀ k, cZ.π.app k ≫ g.app k = E.inv ≫ cO.π.app k := by
    intro k
    rw [← hE k]
    simp
  have hOq : ∀ k, cO.π.app k ≫ ι.app k ≫ qY.app k = E.hom ≫ a ≫ α0 := by
    intro k
    calc cO.π.app k ≫ ι.app k ≫ qY.app k
        = E.hom ≫ cZ.π.app k ≫ (g.app k ≫ ι.app k) ≫ qY.app k := by
          rw [← hE k]
          simp
      _ = E.hom ≫ (cZ.π.app k ≫ qZ.app k) ≫ α0 := by
          rw [hgk, ← hq]
          simp
      _ = E.hom ≫ a ≫ α0 := by rw [ha]
  obtain ⟨i, h, hh1, hh2⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    O tO pZ0 cO hO (E.hom ≫ a) (by
      refine NatTrans.ext (funext fun k => ?_)
      rw [NatTrans.comp_app, htO, Functor.const_map_app, reassoc_of% (hOq k), hα0]
      simp)
  obtain ⟨k, u, hu⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    DZ tZ pZ0 cZ hcZ (g.app i ≫ h) (qZ.app i)
    (by
      simp only [htZ, Category.assoc, hh2, htO]
      rw [reassoc_of% (hgk i), reassoc_of% (hq i).symm, hα0])
    (htZ i)
    (by
      rw [reassoc_of% (hcZg i), hh1]
      simp [ha])
  obtain ⟨k', v, hv⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    O tO pY0 cO hO (h ≫ α0) (ι.app i ≫ qY.app i)
    (by rw [Category.assoc, hα0, hh2])
    (by rw [htO]; simp only [Category.assoc])
    (by rw [reassoc_of% hh1, hOq])
  obtain ⟨m, w1, w2, hw⟩ := IsCofiltered.cospan u v
  have hZm : (O.map (w1 ≫ u) ≫ h) ≫ pZ0 = (ι.app m ≫ pY.app m) ≫ qB.app m := by
    rw [Category.assoc, hh2, NatTrans.naturality]
    simp [htO, (hY m).w]
  let s := (hZ m).lift (O.map (w1 ≫ u) ≫ h) (ι.app m ≫ pY.app m) hZm
  refine ⟨m, ⟨⟨s, ?_, ?_⟩⟩⟩
  · apply (hZ m).hom_ext
    · rw [Category.assoc, (hZ m).lift_fst, Category.id_comp, ← g.naturality_assoc,
        Functor.map_comp, Category.assoc, hu, ← Category.assoc, ← Functor.map_comp,
        qZ.naturality]
      simp
    · rw [Category.assoc, (hZ m).lift_snd, Category.id_comp, reassoc_of% (hgk m), hαk m]
  · rw [← cancel_mono (ι.app m), Category.assoc, hgk m, Category.id_comp]
    apply (hY m).hom_ext
    · rw [Category.assoc, ← hq m, ← Category.assoc, (hZ m).lift_fst, hw, Functor.map_comp]
      simp only [Category.assoc]
      rw [hv, ← Functor.map_comp_assoc, ι.naturality_assoc, qY.naturality]
      simp
    · rw [Category.assoc, hαk m, (hZ m).lift_snd]

private noncomputable def toConst {I : Type} [SmallCategory I] (D : I ⥤ Scheme.{0}) {j i0 : I}
    (e0 : j ⟶ i0) : Over.forget j ⋙ D ⟶ (Functor.const (Over j)).obj (D.obj i0) where
  app k := D.map (k.hom ≫ e0)
  naturality k k' f := by
    have := Over.w f
    simp only [Functor.comp_map, Over.forget_map, Functor.const_obj_map, Category.comp_id,
      Functor.comp_obj, Over.forget_obj, Functor.const_obj_obj]
    rw [← D.map_comp, reassoc_of% this]

theorem UpperTheory.limit_compact_of_cofiltered_cartesian_affine_transition :
    ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (B DZ DY : I ⥤ Scheme.{0})
        [∀ {i j : I} (f : i ⟶ j), IsAffineHom (B.map f)]
        (α : DZ ⟶ DY) (pZ : DZ ⟶ B) (pY : DY ⟶ B), α ≫ pY = pZ →
        (∀ {i j : I} (f : i ⟶ j), IsPullback (DZ.map f) (pZ.app i) (pZ.app j) (B.map f)) →
        (∀ {i j : I} (f : i ⟶ j), IsPullback (DY.map f) (pY.app i) (pY.app j) (B.map f)) →
        ∀ (cZ : Cone DZ) (_ : IsLimit cZ) (cY : Cone DY) (_ : IsLimit cY),
        (∀ i, CompactSpace (DZ.obj i)) → (∀ i, QuasiSeparatedSpace (DZ.obj i)) →
        (∀ i, CompactSpace (DY.obj i)) → (∀ i, QuasiSeparatedSpace (DY.obj i)) →
        ∀ (i0 : I), LocallyOfFinitePresentation (pZ.app i0) → LocallyOfFiniteType (pY.app i0) →
        ∀ (m : cZ.pt ⟶ cY.pt) [IsOpenImmersion m], (∀ i, cZ.π.app i ≫ α.app i = m ≫ cY.π.app i) →
        ∀ (j : I) (_ : j ⟶ i0) (V : (DY.obj j).Opens), IsCompact (V : Set (DY.obj j)) →
          α.app j ⁻¹ᵁ V = ⊤ → cY.π.app j ⁻¹ᵁ V = m.opensRange →
          ∃ (l : I) (_ : l ⟶ j), IsOpenImmersion (α.app l) := by
  intro I _ _ B DZ DY _ α pZ pY hα hZpb hYpb cZ hcZ cY hcY hcZ1 hqZ1 hcY1 hqY1 i0 _ _ m _ hm j e0 V
    hV hαV hmV
  have hDZaff : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (DZ.map f) := fun f =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) (hZpb f).flip
      inferInstance
  have hDYaff : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (DY.map f) := fun f =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) (hYpb f).flip
      inferInstance
  have hDZaff' : ∀ {a b : Over j} (f : a ⟶ b), IsAffineHom ((Over.forget j ⋙ DZ).map f) :=
    fun f => hDZaff f.left
  have hDZc' : ∀ k : Over j, CompactSpace ((Over.forget j ⋙ DZ).obj k) := fun k => hcZ1 k.left
  let O := opensDiagram DY j V
  let ι : O ⟶ Over.forget j ⋙ DY := opensDiagramι DY j V
  let α' : Over.forget j ⋙ DZ ⟶ Over.forget j ⋙ DY := Functor.whiskerLeft (Over.forget j) α
  have hOc : ∀ k : Over j, CompactSpace (O.obj k) := fun k =>
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := DY.map k.hom) _ V.2 hV)
  have hOq : ∀ k : Over j, QuasiSeparatedSpace (O.obj k) := fun k => by
    haveI : QuasiSeparatedSpace ((Over.forget j ⋙ DY).obj k) := hqY1 k.left
    exact quasiSeparatedSpace_of_quasiSeparated (ι.app k)
  have hrange : ∀ k : Over j, Set.range (α'.app k) ⊆ Set.range (ι.app k) := by
    intro k y hy
    obtain ⟨x, rfl⟩ := hy
    have hpre : α.app k.left ⁻¹ᵁ (DY.map k.hom ⁻¹ᵁ V) = ⊤ := by
      rw [← Scheme.Hom.comp_preimage, ← α.naturality, Scheme.Hom.comp_preimage, hαV]
      simp
    have hx : x ∈ α.app k.left ⁻¹ᵁ (DY.map k.hom ⁻¹ᵁ V) := by
      rw [hpre]
      trivial
    exact ⟨⟨_, hx⟩, rfl⟩
  let g : Over.forget j ⋙ DZ ⟶ O :=
    { app := fun k => IsOpenImmersion.lift (ι.app k) (α'.app k) (hrange k)
      naturality := by
        intro k k' f
        rw [← cancel_mono (ι.app k'), Category.assoc, Category.assoc, ι.naturality]
        simp only [IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac_assoc]
        exact α'.naturality f }
  have hgk : ∀ k, g.app k ≫ ι.app k = α'.app k := fun k => IsOpenImmersion.lift_fac _ _ _
  let E : (cY.π.app j ⁻¹ᵁ V).toScheme ≅ cZ.pt :=
    IsOpenImmersion.isoOfRangeEq (cY.π.app j ⁻¹ᵁ V).ι m (by simp [hmV])
  have hE : ∀ k : Over j, E.hom ≫ (cZ.whisker (Over.forget j)).π.app k ≫ g.app k =
      (opensCone DY cY j V).π.app k := by
    intro k
    apply (cancel_mono (ι.app k)).mp
    simp only [Category.assoc, hgk]
    have h1 : (cZ.whisker (Over.forget j)).π.app k ≫ α'.app k = m ≫ cY.π.app k.left := hm k.left
    have h2 : E.hom ≫ m = (cY.π.app j ⁻¹ᵁ V).ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    have h3 : E.hom ≫ m ≫ cY.π.app k.left = (cY.π.app j ⁻¹ᵁ V).ι ≫ cY.π.app k.left := by
      rw [reassoc_of% h2]
    have h4 : (opensCone DY cY j V).π.app k ≫ ι.app k =
        (cY.π.app j ⁻¹ᵁ V).ι ≫ cY.π.app k.left := Scheme.Hom.resLE_comp_ι _ _
    rw [h1]
    exact h3.trans h4.symm
  obtain ⟨k, hk⟩ := core (J := Over j) (Over.forget j ⋙ B) (Over.forget j ⋙ DZ)
    (Over.forget j ⋙ DY) O (B.obj i0) (DZ.obj i0) (DY.obj i0)
    (Functor.whiskerLeft (Over.forget j) pZ) (Functor.whiskerLeft (Over.forget j) pY)
    α' ι g
    (NatTrans.ext (funext fun k => hgk k))
    (NatTrans.ext (funext fun k => by simpa [α'] using congr_app hα k.left))
    (toConst B e0) (toConst DZ e0) (toConst DY e0) (pZ.app i0) (pY.app i0) (α.app i0)
    (by simpa using congr_app hα i0)
    (fun k => by simp [toConst, α', α.naturality])
    (fun k => hZpb _) (fun k => hYpb _)
    (opensCone DY cY j V) (isLimitOpensCone DY cY hcY j V)
    (cZ.whisker (Over.forget j)) ((Functor.Initial.isLimitWhiskerEquiv (Over.forget j) cZ).symm hcZ)
    E hE (cZ.π.app i0) (fun k => by simp [toConst])
  refine ⟨k.left, k.hom, ?_⟩
  show IsOpenImmersion (α'.app k)
  rw [← hgk k]
  infer_instance
