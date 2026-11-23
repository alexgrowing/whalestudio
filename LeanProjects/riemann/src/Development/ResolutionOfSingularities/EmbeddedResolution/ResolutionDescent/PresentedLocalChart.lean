import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimension
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceZeroSection
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothPullbackLocalAmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceChartPresentation
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ClosedEmbeddingIntoAffineSpace
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BasicOpenClosedEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothLocalChart
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure PresentedLocalChart {k : Type u} [Field k] [CharZero k] {Y V : Scheme.{u}}
    {pY : Y ⟶ Spec (CommRingCat.of k)} {pV : V ⟶ Spec (CommRingCat.of k)}
    {G : EmbeddingDatum k Y pY} (P : ClosedEmbeddingIntoAffineSpace G) (H : EmbeddingDatum k V pV)
    (u : V ⟶ Y) (r : ℕ) (y : ↥V) extends SmoothLocalChart G H u y where
  threshold : ℕ
  presentation : ∀ N : ℕ, threshold ≤ N →
    ∃ σ : ambient ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N + 1))),
      AlgebraicGeometry.IsClosedImmersion σ ∧
      σ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (P.dim + N + 1))) = ambientStruct ∧
      HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (P.dim + N + 1)))) σ
        (P.codimBound + (N - r) + 1)
  le_threshold : r ≤ threshold

theorem nonempty_presentedLocalChart (hS : SmoothPullbackHasLocalAmbientEmbedding.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] [CharZero k] (Y V : Scheme.{u})
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsAffine V]
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pV : V ⟶ Spec (CommRingCat.of k))
    (G : EmbeddingDatum k Y pY) (P : ClosedEmbeddingIntoAffineSpace G) (H : EmbeddingDatum k V pV)
    (u : V ⟶ Y) (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r u]
    (hu : u ≫ pY = pV) (y : ↥V) :
    Nonempty (PresentedLocalChart P H u r y) := by
  classical
  obtain ⟨V₀, hyV₀, hV₀aff, A', pA', hA'aff, hA'sm, hA'ft, hA'qc, gg, hgsm, hgp, jj, hjci,
      hjpb, N₀, hrN₀, hpres⟩ :=
    hS k Y V G.ambient pY pV G.ambientStruct G.emb G.comp_eq P.dim P.codimBound P.toAffine
      P.toAffine_comp P.locallyConstCodim r u hu y
  have := hA'aff
  have := hA'sm
  have := hA'ft
  have := hA'qc
  have := hgsm
  have := hjci
  obtain ⟨σ₀, hσ₀ci, hσ₀comp, hσ₀codim⟩ := hpres N₀ le_rfl
  have := hσ₀ci
  have hembCI : AlgebraicGeometry.IsClosedImmersion H.emb := H.isClosedImmersion_emb
  have hind := H.emb.isClosedEmbedding.toIsEmbedding.toIsInducing
  obtain ⟨Ω, hΩ, hΩeq⟩ := hind.isOpen_iff.mp V₀.isOpen
  have hyΩ : H.emb.base y ∈ Ω := by
    have h0 : y ∈ ⇑H.emb.base ⁻¹' Ω := by rw [hΩeq]; exact hyV₀
    exact h0
  obtain ⟨Ubase, hUmem, hyU, hUΩ⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen H.ambient)
      (U := (⟨Ω, hΩ⟩ : H.ambient.Opens)) (x := H.emb.base y) hyΩ
  obtain ⟨func, rfl⟩ := hUmem
  have hymem : y ∈ (H.emb ⁻¹ᵁ H.ambient.basicOpen func) := hyU
  have hsub : (H.emb ⁻¹ᵁ H.ambient.basicOpen func) ≤ V₀ := by
    intro x hx
    have hx1 : H.emb.base x ∈ H.ambient.basicOpen func := hx
    have hx2 : x ∈ ⇑H.emb.base ⁻¹' Ω := hUΩ hx1
    rw [hΩeq] at hx2
    exact hx2
  obtain ⟨L, hL⟩ : ∃ L : Γ(affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N₀))), ⊤),
      (ConcreteCategory.hom (Scheme.Hom.appTop (jj ≫ σ₀))) L
        = (ConcreteCategory.hom (Scheme.Hom.appTop (V₀.ι ≫ H.emb))) func :=
    ⟨_, appTop_globalSectionLift k (P.dim + N₀) (jj ≫ σ₀) _⟩
  obtain ⟨Fsec, hopen⟩ : ∃ Fsec : Γ(A', ⊤),
      jj ⁻¹ᵁ (A'.basicOpen Fsec) = V₀.ι ⁻¹ᵁ (H.emb ⁻¹ᵁ H.ambient.basicOpen func) := by
    refine ⟨(ConcreteCategory.hom (Scheme.Hom.appTop σ₀)) L, ?_⟩
    have eA : A'.basicOpen ((ConcreteCategory.hom (Scheme.Hom.appTop σ₀)) L)
        = σ₀ ⁻¹ᵁ ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N₀)))).basicOpen L) :=
      (Scheme.preimage_basicOpen σ₀ L).symm
    have e1 : jj ⁻¹ᵁ
          (σ₀ ⁻¹ᵁ ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N₀)))).basicOpen L))
        = (jj ≫ σ₀) ⁻¹ᵁ
          ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N₀)))).basicOpen L) := rfl
    have eB : (jj ≫ σ₀) ⁻¹ᵁ
          ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N₀)))).basicOpen L)
        = (↑V₀ : Scheme.{u}).basicOpen
            ((ConcreteCategory.hom (Scheme.Hom.appTop (jj ≫ σ₀))) L) :=
      Scheme.preimage_basicOpen _ _
    have e2 : V₀.ι ⁻¹ᵁ (H.emb ⁻¹ᵁ H.ambient.basicOpen func)
        = (V₀.ι ≫ H.emb) ⁻¹ᵁ (H.ambient.basicOpen func) := rfl
    have eC : (V₀.ι ≫ H.emb) ⁻¹ᵁ (H.ambient.basicOpen func)
        = (↑V₀ : Scheme.{u}).basicOpen
            ((ConcreteCategory.hom (Scheme.Hom.appTop (V₀.ι ≫ H.emb))) func) :=
      Scheme.preimage_basicOpen _ _
    rw [eA, e1, eB, hL, e2, eC]
  obtain ⟨θ, hθ⟩ : ∃ θ : (H.emb ⁻¹ᵁ H.ambient.basicOpen func).toScheme ≅
      (jj ⁻¹ᵁ A'.basicOpen Fsec).toScheme,
      θ.hom ≫ ((jj ⁻¹ᵁ A'.basicOpen Fsec).ι ≫ V₀.ι)
        = (H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι := by
    have hrange : Set.range ⇑(H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι.base
        = Set.range ⇑((jj ⁻¹ᵁ A'.basicOpen Fsec).ι ≫ V₀.ι).base := by
      have hcomp : Set.range ⇑((jj ⁻¹ᵁ A'.basicOpen Fsec).ι ≫ V₀.ι).base
          = ⇑V₀.ι.base '' Set.range ⇑(jj ⁻¹ᵁ A'.basicOpen Fsec).ι.base := by
        simp [Set.range_comp]
      rw [hcomp, hopen, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      have h4 : (↑(V₀.ι ⁻¹ᵁ (H.emb ⁻¹ᵁ H.ambient.basicOpen func)) : Set ↥V₀.toScheme)
          = ⇑V₀.ι.base ⁻¹' (↑(H.emb ⁻¹ᵁ H.ambient.basicOpen func) : Set ↥V) := rfl
      rw [h4, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
      exact (Set.inter_eq_self_of_subset_left (fun x hx => hsub hx)).symm
    exact ⟨AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq _ _ hrange,
      AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange⟩
  have hθ' : (θ.hom ≫ (jj ⁻¹ᵁ A'.basicOpen Fsec).ι) ≫ V₀.ι
      = (H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι := by
    rw [Category.assoc]; exact hθ
  have hpb1 : CategoryTheory.IsPullback
      (AlgebraicGeometry.morphismRestrict jj (A'.basicOpen Fsec))
      ((jj ⁻¹ᵁ A'.basicOpen Fsec).ι ≫ (V₀.ι ≫ u)) ((A'.basicOpen Fsec).ι ≫ gg) G.emb :=
    (AlgebraicGeometry.isPullback_morphismRestrict jj (A'.basicOpen Fsec)).paste_vert hjpb
  have hcomm : CategoryTheory.CommSq θ.hom
      ((H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι ≫ u)
      ((jj ⁻¹ᵁ A'.basicOpen Fsec).ι ≫ (V₀.ι ≫ u)) (𝟙 Y) := by
    constructor
    rw [Category.comp_id, ← Category.assoc, ← Category.assoc, hθ']
  have hiso : CategoryTheory.IsPullback θ.hom
      ((H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι ≫ u)
      ((jj ⁻¹ᵁ A'.basicOpen Fsec).ι ≫ (V₀.ι ≫ u)) (𝟙 Y) :=
    CategoryTheory.IsPullback.of_horiz_isIso hcomm
  have hpb : CategoryTheory.IsPullback
      (θ.hom ≫ AlgebraicGeometry.morphismRestrict jj (A'.basicOpen Fsec))
      ((H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι ≫ u)
      ((A'.basicOpen Fsec).ι ≫ gg) G.emb := by
    have h5 := hiso.paste_horiz hpb1
    rwa [Category.id_comp] at h5
  have hambaff : AlgebraicGeometry.IsAffine (A'.basicOpen Fsec).toScheme :=
    (AlgebraicGeometry.isAffineOpen_top A').basicOpen Fsec
  refine ⟨{
    func := func
    mem_domain := hymem
    ambient := (A'.basicOpen Fsec).toScheme
    ambientStruct := (A'.basicOpen Fsec).ι ≫ pA'
    isAffine_ambient := hambaff
    smooth_ambientStruct := by infer_instance
    locallyOfFiniteType_ambientStruct := by infer_instance
    quasiCompact_ambientStruct := by infer_instance
    toAmbient := (A'.basicOpen Fsec).ι ≫ gg
    smooth_toAmbient := by infer_instance
    comp_eq := by rw [Category.assoc, hgp]
    imm := θ.hom ≫ AlgebraicGeometry.morphismRestrict jj (A'.basicOpen Fsec)
    isClosedImmersion_imm := by
      have : AlgebraicGeometry.IsClosedImmersion
          (AlgebraicGeometry.morphismRestrict jj (A'.basicOpen Fsec)) := by infer_instance
      infer_instance
    isPullback := hpb
    threshold := N₀
    le_threshold := hrN₀
    presentation := by
      intro N hN
      obtain ⟨σ, hσci, hσcomp, hσcodim⟩ := hpres N hN
      have := hσci
      refine ⟨basicOpenEmbedding k (P.dim + N) σ Fsec ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} (P.dim + N) 1)
            (Spec (CommRingCat.of k))).hom, by infer_instance, ?_, ?_⟩
      · rw [Category.assoc, affineSpaceIsoOfEquiv_hom_comp_toSpec]
        exact basicOpenEmbedding_comp_affineSpaceIndexedByToSpec k (P.dim + N) σ Fsec pA' hσcomp
      · exact hasSmoothCoordCodim_basicOpenEmbedding hsm k (P.dim + N)
          (P.codimBound + (N - r)) σ Fsec hσcodim }⟩

end FunctorialResolution.EmbeddedResolution

end
