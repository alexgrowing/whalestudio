import Mathlib
import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
import Development.AutomorphicArithmetic.CommutativeAlgebra.ClopProjFiniteEtaleOfIsClosed
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsOpenImmersionOfClosedImmersionFlatEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSchemeFiniteLocallyFreeRepresentablePropeStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

private lemma UpperTheory.exists_isPullback_iff_preimage {V₀ X' U₀ X : Scheme.{0}} (v : V₀ ⟶ X') (m : X' ⟶ X) (u : U₀ ⟶ X)
    [IsOpenImmersion v] [IsOpenImmersion u] :
    (∃ w, IsPullback v w m u) ↔ m ⁻¹ᵁ u.opensRange = v.opensRange := by
  constructor
  · rintro ⟨w, hw⟩
    ext x
    change x ∈ m ⁻¹' Set.range u ↔ x ∈ Set.range v
    rw [← Scheme.Pullback.range_fst]
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨hw.isoPullback.inv b, ?_⟩
      rw [← Scheme.Hom.comp_apply, hw.isoPullback_inv_fst]
    · rintro ⟨a, rfl⟩
      refine ⟨hw.isoPullback.hom a, ?_⟩
      rw [← Scheme.Hom.comp_apply, hw.isoPullback_hom_fst]
  · intro h
    have hr : Set.range v = Set.range (pullback.fst m u) := by
      rw [Scheme.Pullback.range_fst]
      have := congrArg (fun O : X'.Opens => (O : Set X')) h
      exact this.symm
    let e := IsOpenImmersion.isoOfRangeEq v (pullback.fst m u) hr
    refine ⟨e.hom ≫ pullback.snd m u, IsPullback.of_iso_pullback ⟨?_⟩ e ?_ rfl⟩
    · rw [← IsOpenImmersion.isoOfRangeEq_hom_fac v (pullback.fst m u) hr, Category.assoc,
        pullback.condition, Category.assoc]
    · exact IsOpenImmersion.isoOfRangeEq_hom_fac v (pullback.fst m u) hr

private lemma UpperTheory.pullback_map_symmetry_whisker {S : Scheme.{0}} {T Y G : Over S} (y : T ⟶ Y) :
    pullback.map G.hom T.hom G.hom Y.hom (𝟙 _) y.left (𝟙 S) (by simp) (by simp) ≫
        (pullbackSymmetry G.hom Y.hom).hom =
      (pullbackSymmetry G.hom T.hom).hom ≫ (y ▷ G).left := by
  apply pullback.hom_ext <;> simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
    pullbackSymmetry_hom_comp_snd]
  · erw [pullback.lift_snd]
    simp
  · erw [pullback.lift_fst]
    simp

private lemma UpperTheory.isPullback_transport_symmetry {S : Scheme.{0}} {T Y G : Over S} (y : T ⟶ Y)
    (V : (T ⊗ G).left.Opens) {U₀ : Scheme.{0}} (u : U₀ ⟶ pullback G.hom Y.hom) (w : (V : Scheme.{0}) ⟶ U₀) :
    IsPullback (V.ι ≫ (pullbackSymmetry G.hom T.hom).inv) w
        (pullback.map G.hom T.hom G.hom Y.hom (𝟙 _) y.left (𝟙 S) (by simp) (by simp)) u ↔
      IsPullback V.ι w (y ▷ G).left (u ≫ (pullbackSymmetry G.hom Y.hom).hom) := by
  have hsq := UpperTheory.pullback_map_symmetry_whisker (G := G) y
  constructor
  · intro h
    refine h.of_iso (Iso.refl _) (pullbackSymmetry G.hom T.hom) (Iso.refl _)
      (pullbackSymmetry G.hom Y.hom) ?_ ?_ ?_ ?_
    · simp
    · simp
    · exact hsq
    · simp
  · intro h
    refine h.of_iso (Iso.refl _) (pullbackSymmetry G.hom T.hom).symm (Iso.refl _)
      (pullbackSymmetry G.hom Y.hom).symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp only [Iso.symm_hom]
      rw [Iso.eq_inv_comp, ← Category.assoc, ← hsq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · simp

theorem UpperTheory.exists_clopRepOfRank_of_locallyNoetherian :
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S), IsFinite G.hom → Etale G.hom → ∀ r : ℕ, ∃ (Y : Over S) (U : (Y ⊗ G).left.Opens), UpperTheory.RepresentationRank.RepOfRank r G Y U := by
  intro S _ G hfin het r
  obtain ⟨H, h, U₀, u, hprop, hcl, hfin', hflat', hrk, huniv⟩ :=
    GlobalTheory.T.hilbertScheme_finite_locallyFree_representable_proper S G.left G.hom hfin inferInstance inferInstance r
  haveI := hprop
  haveI := hcl
  haveI := hfin'
  haveI := hflat'
  haveI : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian h
  haveI : Etale (pullback.snd G.hom h) := inferInstance
  haveI : IsOpenImmersion u :=
    UpperTheory.isOpenImmersion_of_closedImmersion_flat_etale u (pullback.snd G.hom h) inferInstance hcl hflat' inferInstance
  let Y : Over S := Over.mk h
  let ι₀ : U₀ ⟶ (Y ⊗ G).left := u ≫ (pullbackSymmetry G.hom Y.hom).hom
  haveI : IsOpenImmersion ι₀ := by dsimp [ι₀]; infer_instance
  haveI : IsClosedImmersion ι₀ := by dsimp [ι₀]; infer_instance
  refine ⟨Y, ι₀.opensRange, ?_, ?_, ?_⟩
  · exact ι₀.isClosedEmbedding.isClosed_range
  · intro y
    have hp : UpperTheory.RepresentationRank.proj ι₀.opensRange = ι₀.isoOpensRange.inv ≫ (u ≫ pullback.snd G.hom h) := by
      rw [Iso.eq_inv_comp]
      change ι₀.isoOpensRange.hom ≫ (ι₀.opensRange.ι ≫ pullback.fst Y.hom G.hom) = _
      rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
      simp [ι₀, Y]
    rw [hp, Scheme.Hom.finrank_comp_left_of_isIso]
    exact hrk y
  · intro T V hV hVr
    obtain ⟨hVF, hVE⟩ := UpperTheory.clopProj_finite_etale_of_isClosed V hfin het hV
    haveI := hVF
    haveI := hVE
    let v : (V : Scheme.{0}) ⟶ pullback G.hom T.hom := V.ι ≫ (pullbackSymmetry G.hom T.hom).inv
    haveI : IsClosedImmersion V.ι :=
      IsClosedImmersion.of_isPreimmersion V.ι (by rw [Scheme.Opens.range_ι]; exact hV)
    haveI : IsClosedImmersion v := by dsimp [v]; infer_instance
    have hvp : v ≫ pullback.snd G.hom T.hom = UpperTheory.RepresentationRank.proj V := by
      simp [v, UpperTheory.RepresentationRank.proj]
    haveI : IsFinite (v ≫ pullback.snd G.hom T.hom) := by rw [hvp]; exact hVF
    haveI : Flat (v ≫ pullback.snd G.hom T.hom) := by rw [hvp]; infer_instance
    obtain ⟨f, ⟨hf, w, hw⟩, huniq⟩ := huniv T.left T.hom V v inferInstance inferInstance
      inferInstance (fun t => by rw [hvp]; exact hVr t)
    have key : ∀ y' : T ⟶ Y, ((y' ▷ G).left ⁻¹ᵁ ι₀.opensRange = V ↔
        ∃ w, IsPullback v w
          (pullback.map G.hom T.hom G.hom Y.hom (𝟙 _) y'.left (𝟙 S) (by simp) (by simp)) u) := by
      intro y'
      have h1 := UpperTheory.exists_isPullback_iff_preimage V.ι (y' ▷ G).left ι₀
      rw [Scheme.Opens.opensRange_ι] at h1
      rw [← h1]
      exact exists_congr fun w => (UpperTheory.isPullback_transport_symmetry y' V u w).symm
    refine ⟨Over.homMk f hf, (key _).mpr ⟨w, hw⟩, ?_⟩
    intro y' hy'
    obtain ⟨w', hw'⟩ := (key y').mp hy'
    exact Over.OverMorphism.ext (huniq y'.left ⟨Over.w y', w', hw'⟩)
