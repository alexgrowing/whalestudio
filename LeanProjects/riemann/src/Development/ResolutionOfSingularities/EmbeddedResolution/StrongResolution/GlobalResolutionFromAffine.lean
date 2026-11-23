import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SubordinateAffineCover
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRuleCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GluedBlowupSequenceExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.InducedRuleFieldExtension
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackUpToEmptyCenters
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.StandardSmoothCharts
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionData
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionCenters
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionDense
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionProper
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionStrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionSmooth
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SmoothLocusIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrongResolution
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def IsCompatibleWithSmoothOfRelativeDimension (B : AffineResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y V : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pV : V ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsAffine V]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced V]
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.LocallyOfFiniteType pV] [AlgebraicGeometry.QuasiCompact pV]
    (u : V ⟶ Y) (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r u],
    u ≫ pY = pV → IsPullbackBlowupSequence u (B k V pV) (B k Y pY)

theorem isCompatibleWithSmoothOfRelativeDimension_affineResolutionRule (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) :
    IsCompatibleWithSmoothOfRelativeDimension (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) := by
  intro k _ _ Y V pY pV _ _ _ _ _ _ _ _ u r _ hu
  exact isPullbackBlowupSequence_affineResolutionRuleOfPrincipalization_of_smooth A hAlg hw hemb hsncE hsm hex hcmp
    k Y V pY pV u r hu

private theorem smoothOfRelativeDimension_comp_zero {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r f]
    [AlgebraicGeometry.SmoothOfRelativeDimension 0 g] :
    AlgebraicGeometry.SmoothOfRelativeDimension r (f ≫ g) := by
  have h : AlgebraicGeometry.SmoothOfRelativeDimension (r + 0) (f ≫ g) := inferInstance
  simpa using h

private theorem smoothOfRelativeDimension_zero_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension 0 f]
    [AlgebraicGeometry.SmoothOfRelativeDimension r g] :
    AlgebraicGeometry.SmoothOfRelativeDimension r (f ≫ g) := by
  have h : AlgebraicGeometry.SmoothOfRelativeDimension (0 + r) (f ≫ g) := inferInstance
  simpa using h

private theorem opensImage_le_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (Z : X.Opens) (U₀ : Y.Opens)
    (W : Z.toScheme.Opens) (e : W ≤ (Z.ι ≫ f) ⁻¹ᵁ U₀) : Z.ι ''ᵁ W ≤ f ⁻¹ᵁ U₀ := by
  rintro x ⟨w, hw, rfl⟩
  simpa using e hw

private theorem respectsIso_smoothOfRelativeDimension (r : ℕ) :
    MorphismProperty.RespectsIso
      (@AlgebraicGeometry.SmoothOfRelativeDimension r : MorphismProperty Scheme.{u}) := by
  have hL : MorphismProperty.RespectsLeft
      (@AlgebraicGeometry.SmoothOfRelativeDimension r : MorphismProperty Scheme.{u})
      (MorphismProperty.isomorphisms Scheme.{u}) := by
    constructor
    intro X Y Z i hi f hf
    have : CategoryTheory.IsIso i := hi
    have : AlgebraicGeometry.IsOpenImmersion i := inferInstance
    have : AlgebraicGeometry.SmoothOfRelativeDimension 0 i := inferInstance
    have := hf
    exact smoothOfRelativeDimension_zero_comp i f r
  have hR : MorphismProperty.RespectsRight
      (@AlgebraicGeometry.SmoothOfRelativeDimension r : MorphismProperty Scheme.{u})
      (MorphismProperty.isomorphisms Scheme.{u}) := by
    constructor
    intro X Y Z i hi f hf
    have : CategoryTheory.IsIso i := hi
    have : AlgebraicGeometry.IsOpenImmersion i := inferInstance
    have : AlgebraicGeometry.SmoothOfRelativeDimension 0 i := inferInstance
    have := hf
    exact smoothOfRelativeDimension_comp_zero f i r
  exact ⟨⟩

private theorem smoothOfRelativeDimension_of_iSup_eq_top (r : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (H : ∀ i, AlgebraicGeometry.SmoothOfRelativeDimension r ((U i).ι ≫ f)) :
    AlgebraicGeometry.SmoothOfRelativeDimension r f := by
  refine ⟨fun x => ?_⟩
  have htop : x ∈ (⊤ : X.Opens) := trivial
  rw [← hU] at htop
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp htop
  obtain ⟨H'⟩ := H i
  obtain ⟨U₀, hU₀, W, hW, hxW, e, hsm⟩ := H' ⟨x, hi⟩
  have e' : (U i).ι ''ᵁ W ≤ f ⁻¹ᵁ U₀ := opensImage_le_preimage f (U i) U₀ W e
  have hle : W ≤ (U i).ι ⁻¹ᵁ ((U i).ι ''ᵁ W) := by
    intro w hw
    exact ⟨w, hw, rfl⟩
  refine ⟨U₀, hU₀, (U i).ι ''ᵁ W, hW.image_of_isOpenImmersion (U i).ι,
    ⟨⟨x, hi⟩, hxW, rfl⟩, e', ?_⟩
  have h1 := Scheme.Hom.appLE_comp_appLE (U i).ι f U₀ ((U i).ι ''ᵁ W) W e' hle
  have h2 := Scheme.Opens.ι_appLE (U i) ((U i).ι ''ᵁ W) W hle
  have h3 : X.presheaf.map (homOfLE (le_refl ((U i).ι ''ᵁ W))).op
      = 𝟙 (X.presheaf.obj (Opposite.op ((U i).ι ''ᵁ W))) := by
    simp
  have h23 := h2.trans h3
  have key : ((U i).ι ≫ f).appLE U₀ W e = f.appLE U₀ ((U i).ι ''ᵁ W) e' :=
    h1.symm.trans ((congrArg (fun m => f.appLE U₀ ((U i).ι ''ᵁ W) e' ≫ m) h23).trans
      (Category.comp_id _))
  exact Eq.mp (congrArg (fun m =>
    RingHom.IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom m)) key) hsm

private theorem isZariskiLocalAtSource_smoothOfRelativeDimension (r : ℕ) :
    AlgebraicGeometry.IsZariskiLocalAtSource
      (@AlgebraicGeometry.SmoothOfRelativeDimension r : MorphismProperty Scheme.{u}) := by
  have := respectsIso_smoothOfRelativeDimension r
  refine AlgebraicGeometry.IsZariskiLocalAtSource.mk' ?_ ?_
  · intro X Y f U hf
    have := hf
    have : AlgebraicGeometry.SmoothOfRelativeDimension 0 U.ι := inferInstance
    exact smoothOfRelativeDimension_zero_comp U.ι f r
  · intro X Y f ι U hU H
    exact smoothOfRelativeDimension_of_iSup_eq_top r f U hU H

theorem smoothOfRelativeDimension_opensCoprodMapOfRefinement {X' X : Scheme.{u}} (φ : X' ⟶ X) (r : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension r φ] {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    AlgebraicGeometry.SmoothOfRelativeDimension r (opensCoprodMapOfRefinement φ U V β hβ) := by
  have := isZariskiLocalAtSource_smoothOfRelativeDimension r
  have h : ∀ a : κ, AlgebraicGeometry.SmoothOfRelativeDimension r
      (φ.resLE (U (β a)) (V a) (hβ a) ≫ Sigma.ι (fun i => (U i).toScheme) (β a)) := by
    intro a
    have : AlgebraicGeometry.SmoothOfRelativeDimension 0
        (Sigma.ι (fun i => (U i).toScheme) (β a)) := inferInstance
    exact smoothOfRelativeDimension_comp_zero _ _ r
  exact AlgebraicGeometry.IsZariskiLocalAtSource.sigmaDesc h

theorem exists_affine_etale_cover_of_smoothOfRelativeDimension {k : Type u} [Field k]
    {X X' : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.QuasiCompact f]
    [AlgebraicGeometry.IsReduced X]
    [AlgebraicGeometry.LocallyOfFiniteType f'] [AlgebraicGeometry.QuasiCompact f']
    [AlgebraicGeometry.IsReduced X']
    (φ : X' ⟶ X) (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r φ]
    (hφ : φ ≫ f = f') :
    ∃ (W : Scheme.{u}) (q : W ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)
      (W' : Scheme.{u}) (q' : W' ⟶ Spec (CommRingCat.of k)) (c' : W' ⟶ X') (ψ : W' ⟶ W),
      AlgebraicGeometry.IsAffine W ∧ AlgebraicGeometry.IsReduced W ∧
        AlgebraicGeometry.LocallyOfFiniteType q ∧ AlgebraicGeometry.QuasiCompact q ∧
        AlgebraicGeometry.Etale c ∧ AlgebraicGeometry.Surjective c ∧ c ≫ f = q ∧
      AlgebraicGeometry.IsAffine W' ∧ AlgebraicGeometry.IsReduced W' ∧
        AlgebraicGeometry.LocallyOfFiniteType q' ∧ AlgebraicGeometry.QuasiCompact q' ∧
        AlgebraicGeometry.Etale c' ∧ AlgebraicGeometry.Surjective c' ∧ c' ≫ f' = q' ∧
      AlgebraicGeometry.SmoothOfRelativeDimension r ψ ∧ ψ ≫ c = c' ≫ φ ∧ ψ ≫ q = q' := by
  have hcX : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace f
  have hcX' : CompactSpace ↥X' := QuasiCompact.compactSpace_of_compactSpace f'
  obtain ⟨ι, hι, U, hUaff, hUtop⟩ := exists_finite_affine_cover X
  have : Finite ι := hι
  obtain ⟨κ, hκ, V, β, hVaff, hβ, hVtop⟩ := exists_finite_affine_cover_subordinate φ U hUtop
  have : Finite κ := hκ
  have hWaff : AlgebraicGeometry.IsAffine (sigmaOpens X U) := isAffine_sigmaOpens X U hUaff
  have hW'aff : AlgebraicGeometry.IsAffine (sigmaOpens X' V) := isAffine_sigmaOpens X' V hVaff
  have hcW : CompactSpace ↥(sigmaOpens X U) := inferInstance
  have hcW' : CompactSpace ↥(sigmaOpens X' V) := inferInstance
  exact ⟨sigmaOpens X U, sigmaOpensDesc X U ≫ f, sigmaOpensDesc X U,
    sigmaOpens X' V, sigmaOpensDesc X' V ≫ f', sigmaOpensDesc X' V,
    opensCoprodMapOfRefinement φ U V β hβ,
    hWaff, inferInstance, inferInstance,
    quasiCompact_of_compactSpace_of_subsingleton (sigmaOpensDesc X U ≫ f), inferInstance,
    surjective_sigmaOpensDesc X U hUtop, rfl,
    hW'aff, inferInstance, inferInstance,
    quasiCompact_of_compactSpace_of_subsingleton (sigmaOpensDesc X' V ≫ f'), inferInstance,
    surjective_sigmaOpensDesc X' V hVtop, rfl,
    smoothOfRelativeDimension_opensCoprodMapOfRefinement φ r U V β hβ,
    opensCoprodMapOfRefinement_comp_sigmaOpensDesc φ U V β hβ,
    (by rw [← Category.assoc, opensCoprodMapOfRefinement_comp_sigmaOpensDesc, Category.assoc, hφ])⟩

theorem isCompatibleWithSmoothMorphisms_of_isInducedByAffineRule (B : AffineResolutionRule.{u})
    (hB : IsCompatibleWithSmoothOfRelativeDimension B) (R : ResolutionRule.{u})
    (hR : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
      [AlgebraicGeometry.IsReduced Y], IsInducedByAffineRule B k Y p (R k Y p)) :
    IsCompatibleWithSmoothMorphisms R := by
  intro k _ _ X X' f f' _ _ _ _ _ _ φ r _ hφ
  obtain ⟨W, q, c, W', q', c', ψ, hWaff, hWred, hqlft, hqqc, hcet, hcsurj, hcq,
    hW'aff, hW'red, hq'lft, hq'qc, hc'et, hc'surj, hc'q', hψsm, hψc, hψq⟩ :=
    exists_affine_etale_cover_of_smoothOfRelativeDimension f f' φ r hφ
  have := hWaff
  have := hWred
  have := hqlft
  have := hqqc
  have := hcet
  have := hcsurj
  have := hW'aff
  have := hW'red
  have := hq'lft
  have := hq'qc
  have := hc'et
  have := hc'surj
  have := hψsm
  have hsmφ : AlgebraicGeometry.Smooth φ :=
    AlgebraicGeometry.SmoothOfRelativeDimension.smooth r φ
  have hsmψ : AlgebraicGeometry.Smooth ψ :=
    AlgebraicGeometry.SmoothOfRelativeDimension.smooth r ψ
  have hflatφ : AlgebraicGeometry.Flat φ := inferInstance
  have hflatψ : AlgebraicGeometry.Flat ψ := inferInstance
  have hflatc' : AlgebraicGeometry.Flat c' := inferInstance
  have hcs : ∀ y : ↥X, ∃ w, c w = y := fun y => hcsurj.surj y
  have hc's : ∀ y : ↥X', ∃ w, c' w = y := fun y => hc'surj.surj y
  have hA : IsStrictPullbackBlowupSeq c (B k W q) (R k X f) := hR k X f W q c hcq hcs
  have hA' : IsStrictPullbackBlowupSeq c' (B k W' q') (R k X' f') := hR k X' f' W' q' c' hc'q' hc's
  have hC : IsPullbackBlowupSequence ψ (B k W' q') (B k W q) := hB k W W' q q' ψ r hψq
  have h1 : IsStrictPullbackBlowupSeq φ ((R k X f).baseChange φ) (R k X f) :=
    isStrictPullbackSequenceOfBlowups_baseChange (R k X f) φ
  have h2 : IsStrictPullbackBlowupSeq c' (((R k X f).baseChange φ).baseChange c')
      ((R k X f).baseChange φ) :=
    isStrictPullbackSequenceOfBlowups_baseChange ((R k X f).baseChange φ) c'
  have h3 : IsStrictPullbackBlowupSeq (c' ≫ φ) (((R k X f).baseChange φ).baseChange c')
      (R k X f) := h2.comp h1
  have h4 : IsStrictPullbackBlowupSeq ψ ((B k W q).baseChange ψ) (B k W q) :=
    isStrictPullbackSequenceOfBlowups_baseChange (B k W q) ψ
  have h5 : IsStrictPullbackBlowupSeq (c' ≫ φ) ((B k W q).baseChange ψ) (R k X f) := by
    have h5' : IsStrictPullbackBlowupSeq (ψ ≫ c) ((B k W q).baseChange ψ) (R k X f) := h4.comp hA
    rwa [hψc] at h5'
  have h6 := h3.isomorphic h5
  have h7 := h6.withoutIsoBlowups
  have h8 : IsPullbackBlowupSequence ψ ((B k W q).baseChange ψ).withoutIsoBlowups (B k W q) := h4.isPullbackSequenceOfBlowups_withoutIsoBlowups
  have h9 := hC.isomorphic h8
  have h10 := h9.trans h7.symm
  have h11 := h2.withoutIsoBlowups
  have h12 := hA'.isomorphic_of_isomorphic h11 h10
  have h13 : IsPullbackBlowupSequence φ ((R k X f).baseChange φ).withoutIsoBlowups (R k X f) :=
    h1.isPullbackSequenceOfBlowups_withoutIsoBlowups
  exact h13.of_isomorphic h12.symm

private theorem isStrongResolution_of_isInducedByAffineRule_of_isAffine (B : AffineResolutionRule.{u})
    (hres : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
      [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p],
      IsStrongResolution k Y p (B k Y p))
    (hetale : IsCompatibleWithEtaleCovers B)
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) (p : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
    (s : SequenceOfBlowups Y) (hc : IsInducedByAffineRule B k Y p s) :
    IsStrongResolution k Y p s := by
  obtain ⟨W, q, g, hWaff, hWred, hqlft, hqqc, hget, hgsurj, hgq⟩ :=
    exists_affine_etale_cover_of_isReduced Y p
  have := hWaff
  have := hWred
  have := hqlft
  have := hqqc
  have := hget
  have := hgsurj
  have : AlgebraicGeometry.Flat g := inferInstance
  have hsurj : ∀ y : ↥Y, ∃ w, g w = y := fun y => hgsurj.surj y
  have h1 : IsStrictPullbackBlowupSeq g (B k W q) s := hc W q g hgq hsurj
  have h2 : IsStrictPullbackBlowupSeq g (B k W q) (B k Y p) := hetale k Y W p q g hgq hsurj
  exact IsStrongResolution.of_isomorphic k Y p (h2.isomorphic_of_isomorphic h1 (SequenceOfBlowups.isomorphic_refl _)) (hres k Y p)

private theorem isStrongResolution_of_isInducedByAffineRule (B : AffineResolutionRule.{u})
    (hres : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
      [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p],
      IsStrongResolution k Y p (B k Y p))
    (hetale : IsCompatibleWithEtaleCovers B) (R : ResolutionRule.{u})
    (hcomes : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
      [AlgebraicGeometry.IsReduced Y], IsInducedByAffineRule B k Y p (R k Y p))
    (hsmF : IsCompatibleWithSmoothMorphisms R)
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.QuasiCompact f]
    [AlgebraicGeometry.IsReduced X] :
    IsStrongResolution k X f (R k X f) := by
  have hOI : ∀ i : X.affineCover.I₀,
      AlgebraicGeometry.IsOpenImmersion (X.affineCover.f i) := fun _ => inferInstance
  have hA : ∀ i : X.affineCover.I₀,
      AlgebraicGeometry.IsAffine (X.affineCover.X i) := fun _ => inferInstance
  have hRed : ∀ i : X.affineCover.I₀,
      AlgebraicGeometry.IsReduced (X.affineCover.X i) := by
    intro i
    have := hOI i
    exact inferInstance
  have hLFT : ∀ i : X.affineCover.I₀,
      AlgebraicGeometry.LocallyOfFiniteType (X.affineCover.f i ≫ f) := by
    intro i
    have := hOI i
    exact inferInstance
  have hqc : ∀ i : X.affineCover.I₀,
      AlgebraicGeometry.QuasiCompact (X.affineCover.f i ≫ f) := by
    intro i
    have := hA i
    have : CompactSpace ↥(X.affineCover.X i) := inferInstance
    exact quasiCompact_of_compactSpace_of_subsingleton (X.affineCover.f i ≫ f)
  have hCharts : ∀ i : X.affineCover.I₀,
      AlgebraicGeometry.SmoothOfRelativeDimension 0 (X.affineCover.f i) := by
    intro i
    have := hOI i
    exact inferInstance
  have d : LocalResolutionData k f (R k X f) := by
    refine
      { cover := X.affineCover
        seq := fun i =>
          haveI := hLFT i
          haveI := hqc i
          haveI := hRed i
          R k (X.affineCover.X i) (X.affineCover.f i ≫ f)
        isPullback := ?_
        finiteType := hLFT
        isResolution := ?_ }
    · intro i
      have := hLFT i
      have := hqc i
      have := hRed i
      have := hCharts i
      exact hsmF k X (X.affineCover.X i) f (X.affineCover.f i ≫ f)
        (X.affineCover.f i) 0 rfl
    · intro i
      have := hA i
      have := hLFT i
      have := hqc i
      have := hRed i
      exact isStrongResolution_of_isInducedByAffineRule_of_isAffine B hres hetale k (X.affineCover.X i)
        (X.affineCover.f i ≫ f)
        (R k (X.affineCover.X i) (X.affineCover.f i ≫ f))
        (hcomes k (X.affineCover.X i) (X.affineCover.f i ≫ f))
  refine ⟨d.smooth_lastStructMap_comp, d.isProper_lastStructMap, d.isIso_lastStructMap_restrict_smoothLocus, ?_,
    d.centersLieOver_smoothLocusComplement, d.isStrictNormalCrossingsDivisor_reducedInverseImage⟩
  exact d.dense_preimage_smoothLocus

theorem strongResolutionOfSingularitiesCharZero_of_affineResolutionRule (B : AffineResolutionRule.{u})
    (hres : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
      [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p],
      IsStrongResolution k Y p (B k Y p))
    (hetale : IsCompatibleWithEtaleCovers B) (hopen : IsCompatibleWithOpenImmersions B)
    (hfield : IsCompatibleWithFieldBaseChange B) (hsmooth : IsCompatibleWithSmoothOfRelativeDimension B) :
    StrongResolutionOfSingularitiesCharZero.{u} := by
  have hcen : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
      [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
      [AlgebraicGeometry.IsAffine Y] (i : ℕ),
      i < (B k Y p).length → (B k Y p).center i ≠ ⊤ := by
    intro k _ _ Y p _ _ _ _ i hi
    exact AffineResolutionRule.center_ne_top B hopen k Y p i hi
  have H := existsGluedBlowupSequence_of_center_ne_top B hcen hetale
  obtain ⟨R, hcomes⟩ : ∃ R : ResolutionRule.{u},
      ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
        (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
        [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y],
        IsInducedByAffineRule B k Y p (R k Y p) :=
    ⟨fun k _ _ Y p _ _ _ => (H k Y p).choose,
      fun k _ _ Y p _ _ _ => (H k Y p).choose_spec.2⟩
  have hsmF : IsCompatibleWithSmoothMorphisms R :=
    isCompatibleWithSmoothMorphisms_of_isInducedByAffineRule B hsmooth R hcomes
  refine ⟨R, ?_, hsmF, inducedRuleCompatibleWithFieldExtension B hopen hfield R hcomes⟩
  refine (isStrongResolutionRule_iff R).mpr ?_
  intro k _ _ X f _ _ _
  exact isStrongResolution_of_isInducedByAffineRule B hres hetale R hcomes hsmF k X f

theorem strongResolutionOfSingularitiesCharZero_of_principalizationAlgorithm (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm) (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u})
    (haff : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
      [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p],
      IsStrongResolution k Y p (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex k Y p)) :
    StrongResolutionOfSingularitiesCharZero.{u} :=
  strongResolutionOfSingularitiesCharZero_of_affineResolutionRule
    (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) haff
    (isCompatibleWithEtaleCovers_affineResolutionRuleOfPrincipalization A hAlg hw hemb hsncE hsm hex hcmp)
    (isCompatibleWithOpenImmersions_affineResolutionRuleOfPrincipalization A hAlg hw hemb hsncE hsm hex hcmp)
    (isCompatibleWithFieldBaseChange_affineResolutionRuleOfPrincipalization A hAlg hw hemb hsncE hsm hex hcmp)
    (isCompatibleWithSmoothOfRelativeDimension_affineResolutionRule A hAlg hw hemb hsncE hsm hex hcmp)

end FunctorialResolution.EmbeddedResolution

end
