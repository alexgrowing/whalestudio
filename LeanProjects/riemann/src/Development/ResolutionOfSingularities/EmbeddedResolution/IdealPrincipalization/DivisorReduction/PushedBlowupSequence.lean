import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificateMonotone
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorFamilyCenters
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

abbrev pushedMarkedSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    T.SequenceOfBlowups :=
  ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).toMarkedBlowupSequenceData
      T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups

abbrev prependedPushedMarkedSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    T.SequenceOfBlowups :=
  ((BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).toMarkedBlowupSequenceData
      T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups

end DivisorReduction

structure PushedBlowupSequenceProperties (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) : Prop where
  isOpen_preimage_preIdeal :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (j : ℕ) (hj : j < T.boundary.length),
      IsOpen (⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹'
        ((DivisorReduction.containedComponentsIdeal T j hj).support : Set ↥T.scheme))
  ker_pushedEmb_zero_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
      (hj : j < T.boundary.length) (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
      (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
      (hmk : (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
          (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
            T.structMap T.ideal T.mult T.boundary),
      AlgebraicGeometry.Scheme.Hom.ker
          (DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr 0) =
        (T.boundary.get ⟨j, hj⟩).comap
          (DivisorReduction.pushedMarkedSeq hres hno T j hj s hpr hmk).isoZero.hom
  ker_pushedEmb_zero_pre :
    ∀ (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
      (hj : j < T.boundary.length) (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
      (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
      (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
      (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
          (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
            (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
            T.structMap T.ideal T.mult T.boundary),
      AlgebraicGeometry.Scheme.Hom.ker
          (DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
            (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr 0) =
        ((T.boundary.get ⟨j, hj⟩).comap
            (DivisorReduction.prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).isoZero.hom).comap
          ((DivisorReduction.prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).transitionMapSucc 0)
  isSmoothDivisor_boundary_comap :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (j : ℕ) (hj : j < T.boundary.length) (S : T.SequenceOfBlowups),
      IsSmoothDivisor (S.projectionToSpec 0) ((T.boundary.get ⟨j, hj⟩).comap S.isoZero.hom)
  boundaryLocus_subset_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
      (hj : j < T.boundary.length) (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
      (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
      (hmk : (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
          (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
            T.structMap T.ideal T.mult T.boundary),
      ∀ t < s.length,
        s.boundaryLocus t ⊆
          ⇑(DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
              (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t) ⁻¹'
            ((DivisorReduction.pushedMarkedSeq hres hno T j hj s hpr hmk).otherBoundaryLocus j t)
  boundaryLocus_subset_pre :
    ∀ (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
      (hj : j < T.boundary.length) (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
      (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
      (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
      (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
          (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
            (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
            T.structMap T.ideal T.mult T.boundary),
      ∀ t < s.length,
        s.boundaryLocus t ⊆
          ⇑(DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t) ⁻¹'
            ((DivisorReduction.prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).otherBoundaryLocus j (t + 1))
  one_le_mult : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → 1 ≤ T.mult
  isSmoothDivisor_ker_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
      ∀ (j : ℕ) (hj : j < T.boundary.length), DivisorReduction.containedComponentsIdeal T j hj = ⊤ →
        (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
        ∀ [AlgebraicGeometry.IsNoetherian T.scheme] (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
          (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
          (hmk : (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
              (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
                T.structMap T.ideal T.mult T.boundary),
        ∀ t ≤ s.length,
          IsSmoothDivisor ((DivisorReduction.pushedMarkedSeq hres hno T j hj s hpr hmk).projectionToSpec t)
            (AlgebraicGeometry.Scheme.Hom.ker
              (DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
                (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t))
  isSmoothDivisor_ker_pre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
      ∀ (j : ℕ) (hj : j < T.boundary.length), DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
        ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)),
        (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
        ∀ [AlgebraicGeometry.IsNoetherian T.scheme] (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
          (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
          (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
              (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
                T.structMap T.ideal T.mult T.boundary),
        ∀ t ≤ s.length,
          IsSmoothDivisor ((DivisorReduction.prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToSpec (t + 1))
            (AlgebraicGeometry.Scheme.Hom.ker
              (DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t))
  compositeMap_eq_restrictedEmptyCenter :
    ∀ (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
      (hj : j < T.boundary.length) (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
      (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
      (hmk : (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
          (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
            T.structMap T.ideal T.mult T.boundary),
      ∀ t : ℕ,
        s.projectionToSpec t =
          DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
              (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t ≫
            (DivisorReduction.pushedMarkedSeq hres hno T j hj s hpr hmk).projectionToSpec t
  compositeMap_eq_restricted :
    ∀ (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
      (hj : j < T.boundary.length) (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
      (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
      (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
      (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
          (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
            (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
            T.structMap T.ideal T.mult T.boundary),
      ∀ t : ℕ,
        s.projectionToSpec t =
          DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t ≫
            (DivisorReduction.prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToSpec (t + 1)
  support_imageIdeal_subset_ker :
    ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f]
      (I : X.IdealSheafData),
      ((imageIdealSheaf f I).support : Set ↥Y) ⊆
        ((AlgebraicGeometry.Scheme.Hom.ker f).support : Set ↥Y)
  support_preIdeal_subset_boundary :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (j : ℕ) (hj : j < T.boundary.length),
      ((DivisorReduction.containedComponentsIdeal T j hj).support : Set ↥T.scheme) ⊆
        ((T.boundary.get ⟨j, hj⟩).support : Set ↥T.scheme)

private def HasSmoothDivisorTransforms (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (S : T.SequenceOfBlowups) : Prop :=
  ∃ (D : (t : ℕ) → (S.schemeAt t).IdealSheafData) (b : Bool),
    (∀ t ≤ S.length, IsSmoothDivisor (S.projectionToSpec t) (D t)) ∧
    D 0 = (T.boundary.get ⟨j, hj⟩).comap S.isoZero.hom ∧
    (∀ t < S.length,
        ((S.center t).support : Set ↥(S.schemeAt t)) ⊆ ((D t).support : Set ↥(S.schemeAt t))) ∧
    (b = true →
      0 < S.length ∧
      IsOpen (⇑(D 0).subschemeι ⁻¹' (((S.center 0).support : Set ↥(S.schemeAt 0)))) ∧
      D 1 = (D 0).comap (S.transitionMapSucc 0)) ∧
    (∀ t < S.length, (b = true → t ≠ 0) →
        D (t + 1) = Blowup.strictTransform (S.transitionMapSucc t) (S.center t) (D t)) ∧
    (orderAtLeastLocus S.lastIdeal T.mult ∩ ((D S.length).support : Set ↥(S.schemeAt S.length)) = ∅) ∧
    (∀ t < S.length, (b = true → t ≠ 0) →
      ∃ J : (D t).subscheme.IdealSheafData,
        NonzeroOnComponents J ∧
        (∀ x : ↥(D t).subscheme,
            (D t).subschemeι x ∉ S.otherBoundaryLocus j t →
              ∃ V : (D t).subscheme.Opens, x ∈ V ∧
                J.comap V.ι = ((S.ideal t).comap (D t).subschemeι).comap V.ι) ∧
        PrincipalizationCertificate (D t).subscheme ((D t).subschemeι ≫ S.projectionToSpec t) J T.mult
          (⇑(D t).subschemeι ⁻¹' S.otherBoundaryLocus j t)
          ((S.center t).comap (D t).subschemeι))

private theorem divisorReductionShape_of_strictTransforms {T : MarkedIdealWithBoundary.{u}} (j : ℕ) (hj : j < T.boundary.length)
    (S : T.SequenceOfBlowups) (len : ℕ) (D : (t : ℕ) → (S.schemeAt t).IdealSheafData) (hlen : S.length = len)
    (h1 : ∀ t ≤ len, IsSmoothDivisor (S.projectionToSpec t) (D t))
    (h2 : D 0 = (T.boundary.get ⟨j, hj⟩).comap S.isoZero.hom)
    (h3 : ∀ t < len, ((S.center t).support : Set ↥(S.schemeAt t)) ⊆ ((D t).support : Set ↥(S.schemeAt t)))
    (h5 : ∀ t < len, D (t + 1) = Blowup.strictTransform (S.transitionMapSucc t) (S.center t) (D t))
    (h6 : orderAtLeastLocus (S.ideal len) T.mult ∩ ((D len).support : Set ↥(S.schemeAt len)) = ∅)
    (h7 : ∀ t < len, ∃ J : (D t).subscheme.IdealSheafData,
        NonzeroOnComponents J ∧
        (∀ x : ↥(D t).subscheme,
            (D t).subschemeι x ∉ S.otherBoundaryLocus j t →
              ∃ V : (D t).subscheme.Opens, x ∈ V ∧
                J.comap V.ι = ((S.ideal t).comap (D t).subschemeι).comap V.ι) ∧
        PrincipalizationCertificate (D t).subscheme ((D t).subschemeι ≫ S.projectionToSpec t) J T.mult
          (⇑(D t).subschemeι ⁻¹' S.otherBoundaryLocus j t)
          ((S.center t).comap (D t).subschemeι)) :
    HasSmoothDivisorTransforms T j hj S := by
  subst hlen
  refine ⟨D, false, h1, h2, h3, fun hbb => Bool.noConfusion hbb, fun t ht _ => h5 t ht, ?_,
    fun t ht _ => h7 t ht⟩
  rw [MarkedSequenceOfBlowups.lastIdeal_eq]
  exact h6

private theorem divisorReductionShape_of_pullback_then_strictTransforms {T : MarkedIdealWithBoundary.{u}} (j : ℕ) (hj : j < T.boundary.length)
    (S : T.SequenceOfBlowups) (len : ℕ) (hlen : S.length = len + 1)
    (D0 : (S.schemeAt 0).IdealSheafData) (Dd : (t : ℕ) → (S.schemeAt (t + 1)).IdealSheafData)
    (h1a : IsSmoothDivisor (S.projectionToSpec 0) D0)
    (h1b : ∀ t ≤ len, IsSmoothDivisor (S.projectionToSpec (t + 1)) (Dd t))
    (h2 : D0 = (T.boundary.get ⟨j, hj⟩).comap S.isoZero.hom)
    (h3a : ((S.center 0).support : Set ↥(S.schemeAt 0)) ⊆ (D0.support : Set ↥(S.schemeAt 0)))
    (h3b : ∀ t < len, ((S.center (t + 1)).support : Set ↥(S.schemeAt (t + 1))) ⊆
        ((Dd t).support : Set ↥(S.schemeAt (t + 1))))
    (h4 : IsOpen (⇑D0.subschemeι ⁻¹' ((S.center 0).support : Set ↥(S.schemeAt 0))))
    (h4' : Dd 0 = D0.comap (S.transitionMapSucc 0))
    (h5 : ∀ t < len, Dd (t + 1) =
        Blowup.strictTransform (S.transitionMapSucc (t + 1)) (S.center (t + 1)) (Dd t))
    (h6 : orderAtLeastLocus (S.ideal (len + 1)) T.mult ∩
        ((Dd len).support : Set ↥(S.schemeAt (len + 1))) = ∅)
    (h7 : ∀ t < len, ∃ J : (Dd t).subscheme.IdealSheafData,
        NonzeroOnComponents J ∧
        (∀ x : ↥(Dd t).subscheme,
            (Dd t).subschemeι x ∉ S.otherBoundaryLocus j (t + 1) →
              ∃ V : (Dd t).subscheme.Opens, x ∈ V ∧
                J.comap V.ι = ((S.ideal (t + 1)).comap (Dd t).subschemeι).comap V.ι) ∧
        PrincipalizationCertificate (Dd t).subscheme ((Dd t).subschemeι ≫ S.projectionToSpec (t + 1)) J T.mult
          (⇑(Dd t).subschemeι ⁻¹' S.otherBoundaryLocus j (t + 1))
          ((S.center (t + 1)).comap (Dd t).subschemeι)) :
    HasSmoothDivisorTransforms T j hj S := by
  refine ⟨fun t => Nat.rec (motive := fun t => (S.schemeAt t).IdealSheafData) D0
      (fun t' _ => Dd t') t, true, ?_, h2, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (_ | t) ht
    · exact h1a
    · rw [hlen] at ht
      exact h1b t (by omega)
  · rintro (_ | t) ht
    · exact h3a
    · rw [hlen] at ht
      exact h3b t (by omega)
  · intro _
    refine ⟨?_, h4, h4'⟩
    rw [hlen]
    exact Nat.succ_pos len
  · rintro (_ | t) ht hbz
    · exact absurd rfl (hbz rfl)
    · rw [hlen] at ht
      exact h5 t (by omega)
  · rw [MarkedSequenceOfBlowups.lastIdeal_eq, hlen]
    exact h6
  · rintro (_ | t) ht hbz
    · exact absurd rfl (hbz rfl)
    · rw [hlen] at ht
      exact h7 t (by omega)

private theorem comap_imageIdealSheaf_eq_self_of_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsClosedImmersion f] (I : X.IdealSheafData) :
    (imageIdealSheaf f I).comap f = I :=
  Blowup.comap_map_of_isClosedImmersion f I

private theorem orderAtLeastLocus_comap_iso_eq_empty {X Y : Scheme.{u}} (e : X ≅ Y)
    (I : Y.IdealSheafData) (m : ℕ) (h : orderAtLeastLocus I m = (∅ : Set ↥Y)) :
    orderAtLeastLocus (I.comap e.hom) m = (∅ : Set ↥X) := by
  rw [orderAtLeastLocus_comap_iso_hom_eq_preimage, h, Set.preimage_empty]

private theorem exists_principalizationCertificate_ker_of_isClosedImmersion {k : Type u} [Field k]
    {X Y : Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f]
    (pX : X ⟶ Spec (CommRingCat.of k)) (pY : Y ⟶ Spec (CommRingCat.of k))
    (I Z : X.IdealSheafData) (m : ℕ) (Mem : Set ↥X) (MemY : Set ↥Y)
    (IY ZY : Y.IdealSheafData)
    (hp : pX = f ≫ pY)
    (hMem : Mem ⊆ ⇑f ⁻¹' MemY)
    (hIY : IY.comap f = I)
    (hZY : ZY = imageIdealSheaf f Z)
    (hnz : NonzeroOnComponents I)
    (hcert : PrincipalizationCertificate X pX I m Mem Z) :
    ∃ J : (AlgebraicGeometry.Scheme.Hom.ker f).subscheme.IdealSheafData,
      NonzeroOnComponents J ∧
      (∀ x : ↥(AlgebraicGeometry.Scheme.Hom.ker f).subscheme,
          (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι x ∉ MemY →
            ∃ V : (AlgebraicGeometry.Scheme.Hom.ker f).subscheme.Opens, x ∈ V ∧
              J.comap V.ι =
                (IY.comap (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι).comap V.ι) ∧
      PrincipalizationCertificate (AlgebraicGeometry.Scheme.Hom.ker f).subscheme
        ((AlgebraicGeometry.Scheme.Hom.ker f).subschemeι ≫ pY) J m
        (⇑(AlgebraicGeometry.Scheme.Hom.ker f).subschemeι ⁻¹' MemY)
        (ZY.comap (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι) := by
  have hpe : (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι ≫ pY =
      (kerSubschemeIso f).hom ≫ pX := by
    rw [hp, ← Category.assoc, kerSubschemeIso_hom_comp]
  have hid : I.comap (kerSubschemeIso f).hom =
      IY.comap (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι := by
    rw [← hIY, ← kerSubschemeIso_hom_comp f, Scheme.IdealSheafData.comap_comp]
  refine ⟨I.comap (kerSubschemeIso f).hom,
    nonzeroOnComponents_comap_iso_hom (kerSubschemeIso f) I hnz, ?_, ?_⟩
  · intro x _
    refine ⟨⊤, trivial, ?_⟩
    exact congrArg
      (fun J => J.comap (⊤ : (AlgebraicGeometry.Scheme.Hom.ker f).subscheme.Opens).ι) hid
  · have hcert1 := PrincipalizationCertificate.comap_iso_of_eq_iso_hom_comp (kerSubschemeIso f) hpe hcert
    have hsub : ⇑(kerSubschemeIso f).hom ⁻¹' Mem ⊆
        ⇑(AlgebraicGeometry.Scheme.Hom.ker f).subschemeι ⁻¹' MemY := by
      intro x hx
      rw [Set.mem_preimage] at hx
      have h2 := hMem hx
      rw [Set.mem_preimage] at h2
      have hb0 : ⇑(AlgebraicGeometry.Scheme.Hom.ker f).subschemeι x
          = ⇑f (⇑(kerSubschemeIso f).hom x) := by
        rw [← kerSubschemeIso_hom_comp f]
        simp
      rw [Set.mem_preimage, hb0]
      exact h2
    have hZe : ZY.comap (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι
        = Z.comap (kerSubschemeIso f).hom := by
      rw [hZY, ← kerSubschemeIso_hom_comp f, Scheme.IdealSheafData.comap_comp,
        comap_imageIdealSheaf_eq_self_of_isClosedImmersion f Z]
    rw [hZe]
    exact principalizationCertificate_mono_of_subset hsub hcert1

private theorem divisorReductionShape_of_orderAtLeastLocus_empty {T : MarkedIdealWithBoundary.{u}} (j : ℕ)
    (hj : j < T.boundary.length) (S : T.SequenceOfBlowups) (hlen : S.length = 0)
    (hsm : IsSmoothDivisor (S.projectionToSpec 0) ((T.boundary.get ⟨j, hj⟩).comap S.isoZero.hom))
    (hcs : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)) :
    HasSmoothDivisorTransforms T j hj S := by
  refine divisorReductionShape_of_strictTransforms j hj S 0
    (fun t => Nat.rec (motive := fun t => (S.schemeAt t).IdealSheafData)
      ((T.boundary.get ⟨j, hj⟩).comap S.isoZero.hom) (fun _ _ => ⊤) t) hlen ?_ rfl ?_ ?_ ?_ ?_
  · intro t ht
    obtain rfl : t = 0 := Nat.le_zero.mp ht
    exact hsm
  · intro t ht
    exact absurd ht (Nat.not_lt_zero t)
  · intro t ht
    exact absurd ht (Nat.not_lt_zero t)
  · have hz : orderAtLeastLocus (S.ideal 0) T.mult = (∅ : Set ↥(S.schemeAt 0)) := by
      rw [MarkedSequenceOfBlowups.ideal_zero]
      exact orderAtLeastLocus_comap_iso_eq_empty S.isoZero T.ideal T.mult hcs
    rw [hz, Set.empty_inter]
  · intro t ht
    exact absurd ht (Nat.not_lt_zero t)

private theorem ker_embeddingIntoAmbient_succ_eq_strictTransform (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData)
    (E₀ : List T.scheme.IdealSheafData)
    (s : (DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (t : ℕ) (ht : t < s.length) :
    AlgebraicGeometry.Scheme.Hom.ker
        (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj I₀ E₀ s hpr
          (t + 1)) =
      Blowup.strictTransform
        ((DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj I₀ E₀ s hpr).map t)
        ((DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj I₀ E₀ s hpr).center t)
        (AlgebraicGeometry.Scheme.Hom.ker
          (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj I₀ E₀ s hpr
            t)) := by
  have hlt : t < (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.length := by
    rw [show (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.length = s.length from
      MarkedBlowupSequenceData.ofMarkedSequence_length s]
    exact ht
  exact ker_embeddingIntoAmbientBlowupSequence_succ (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres blowupPreservesNoetherian hpr t hlt

private def divisorIdealWithoutBlowup (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    ((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk).schemeAt
      t).IdealSheafData :=
  AlgebraicGeometry.Scheme.Hom.ker
    (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj
      (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t)

private theorem length_ambientMarkedSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary) :
    (DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk).length =
      s.length :=
  DivisorReduction.ambientBlowupSeq_length hres blowupPreservesNoetherian T j hj
    (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr

private theorem isSmoothDivisor_ambientMarkedSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (hV : T.IsAdmissible)
    (hO : T.IsOrderBoundedByMult) (hD : T.IsBalanced hV.locallyOfFiniteType)
    (j : ℕ) (hj : j < T.boundary.length)
    (htop : DivisorReduction.containedComponentsIdeal T j hj = ⊤)
    (hvl : (DivisorReduction.restrictToDivisor T j hj).IsAdmissible)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary) :
    ∀ t ≤ s.length,
      IsSmoothDivisor
        ((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk).projectionToSpec t)
        (divisorIdealWithoutBlowup hres T j hj s hpr hmk t) :=
  hshape.isSmoothDivisor_ker_top T hV hO hD j hj htop hvl s hpr hmk

private theorem divisorTransform_zero_eq_comap_isoObjZero (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary) :
    divisorIdealWithoutBlowup hres T j hj s hpr hmk 0 =
      (T.boundary.get ⟨j, hj⟩).comap
        (DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
          hmk).isoZero.hom :=
  hshape.ker_pushedEmb_zero_top T j hj s hpr hmk

private theorem center_ambientMarkedSeq_eq_imageIdealSheaf (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    (DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk).center t =
      imageIdealSheaf (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t)
        (s.center t) :=
  DivisorReduction.ambientBlowupSeq_center_eq_imageIdealSheaf hres blowupPreservesNoetherian
    T j hj (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t

private theorem support_center_ambientBlowupSeq_subset (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    (((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
          hmk).center t).support :
        Set ↥((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
          hmk).schemeAt t)) ⊆
      ((divisorIdealWithoutBlowup hres T j hj s hpr hmk t).support :
        Set ↥((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
          hmk).schemeAt t)) := by
  have := DivisorReduction.isClosedImmersion_embeddingIntoAmbient hres
    blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
    (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t
  rw [center_ambientMarkedSeq_eq_imageIdealSheaf hres T j hj s hpr hmk t]
  exact hshape.support_imageIdeal_subset_ker _ _
    (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj
      (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t) (s.center t)

private theorem divisorTransform_succ_eq_strictTransform (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary) :
    ∀ t < s.length,
      divisorIdealWithoutBlowup hres T j hj s hpr hmk (t + 1) =
        Blowup.strictTransform
          (((DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s
                hpr).toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary
              hmk).toMarkedSequenceOfBlowups.transitionMapSucc t)
          (((DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s
                hpr).toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary
              hmk).toMarkedSequenceOfBlowups.center t)
          (divisorIdealWithoutBlowup hres T j hj s hpr hmk t) := by
  intro t ht
  rw [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism, MarkedBlowupSequenceData.toMarkedSequence_center]
  exact ker_embeddingIntoAmbient_succ_eq_strictTransform hres T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
    (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t ht

private theorem orderAtLeastLocus_inter_divisorTransform_eq_empty
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (hV : T.IsAdmissible)
    (hO : T.IsOrderBoundedByMult) (hD : T.IsBalanced hV.locallyOfFiniteType)
    (j : ℕ) (hj : j < T.boundary.length)
    (htop : DivisorReduction.containedComponentsIdeal T j hj = ⊤)
    (hvl : (DivisorReduction.restrictToDivisor T j hj).IsAdmissible)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary)
    (hfin : orderAtLeastLocus (s.ideal s.length) T.mult = ∅) :
    orderAtLeastLocus
        ((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk).ideal
          s.length) T.mult ∩
      ((divisorIdealWithoutBlowup hres T j hj s hpr hmk s.length).support :
        Set ↥((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
          hmk).schemeAt s.length)) = ∅ :=
  hfacts.coSupport_inter_ker_eq_empty_top T hV hO hD j hj htop hvl s hpr hfin

private theorem exists_nonzeroOnComponents_certificate_ambientMarkedSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (hV : T.IsAdmissible)
    (hO : T.IsOrderBoundedByMult) (hD : T.IsBalanced hV.locallyOfFiniteType)
    (j : ℕ) (hj : j < T.boundary.length)
    (htop : DivisorReduction.containedComponentsIdeal T j hj = ⊤)
    (hvl : (DivisorReduction.restrictToDivisor T j hj).IsAdmissible)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary)
    (hcert : ∀ t < s.length,
      PrincipalizationCertificate (s.schemeAt t) (s.projectionToSpec t) (s.ideal t) T.mult (s.boundaryLocus t) (s.center t)) :
    ∀ t < s.length,
      ∃ J : (divisorIdealWithoutBlowup hres T j hj s hpr hmk t).subscheme.IdealSheafData,
        NonzeroOnComponents J ∧
        (∀ x : ↥(divisorIdealWithoutBlowup hres T j hj s hpr hmk t).subscheme,
            (divisorIdealWithoutBlowup hres T j hj s hpr hmk t).subschemeι x ∉
                (DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
                  hmk).otherBoundaryLocus j t →
              ∃ V : (divisorIdealWithoutBlowup hres T j hj s hpr hmk t).subscheme.Opens, x ∈ V ∧
                J.comap V.ι =
                  (((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
                      hmk).ideal t).comap
                    (divisorIdealWithoutBlowup hres T j hj s hpr hmk t).subschemeι).comap V.ι) ∧
        PrincipalizationCertificate (divisorIdealWithoutBlowup hres T j hj s hpr hmk t).subscheme
          ((divisorIdealWithoutBlowup hres T j hj s hpr hmk t).subschemeι ≫
            (DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
              hmk).projectionToSpec t) J T.mult
          (⇑(divisorIdealWithoutBlowup hres T j hj s hpr hmk t).subschemeι ⁻¹'
            (DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
              hmk).otherBoundaryLocus j t)
          (((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
            hmk).center t).comap (divisorIdealWithoutBlowup hres T j hj s hpr hmk t).subschemeι) := by
  intro t ht
  have := DivisorReduction.isClosedImmersion_embeddingIntoAmbient hres
    blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
    (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t
  exact exists_principalizationCertificate_ker_of_isClosedImmersion
    (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj
      (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr t)
    (s.projectionToSpec t)
    ((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk).projectionToSpec t)
    (s.ideal t) (s.center t) T.mult (s.boundaryLocus t)
    ((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
      hmk).otherBoundaryLocus j t)
    ((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk).ideal t)
    ((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk).center t)
    (hshape.compositeMap_eq_restrictedEmptyCenter T j hj s hpr hmk t)
    (hshape.boundaryLocus_subset_top T j hj s hpr hmk t ht)
    (hfacts.comap_ctrlIdeal_top T hV hO hD j hj htop hvl s hpr t (le_of_lt ht))
    (center_ambientMarkedSeq_eq_imageIdealSheaf hres T j hj s hpr hmk t)
    (MarkedSequenceOfBlowups.nonzeroOnComponents_ideal_of_isAdmissible effectiveCartierSupportContainsNoComponent hvl s t (le_of_lt ht))
    (hcert t ht)

private theorem divisorReductionShape_ambientBlowupSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (hV : T.IsAdmissible)
    (hO : T.IsOrderBoundedByMult) (hD : T.IsBalanced hV.locallyOfFiniteType)
    (j : ℕ) (hj : j < T.boundary.length)
    (htop : DivisorReduction.containedComponentsIdeal T j hj = ⊤)
    (hvl : (DivisorReduction.restrictToDivisor T j hj).IsAdmissible)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary)
    (hcert : ∀ t < s.length,
      PrincipalizationCertificate (s.schemeAt t) (s.projectionToSpec t) (s.ideal t) T.mult (s.boundaryLocus t) (s.center t))
    (hfin : orderAtLeastLocus (s.ideal s.length) T.mult = ∅) :
    HasSmoothDivisorTransforms T j hj
      (DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk) :=
  divisorReductionShape_of_strictTransforms j hj _ s.length (divisorIdealWithoutBlowup hres T j hj s hpr hmk)
    (length_ambientMarkedSeq hres T j hj s hpr hmk)
    (isSmoothDivisor_ambientMarkedSeq hres hshape T hV hO hD j hj htop hvl s hpr hmk)
    (divisorTransform_zero_eq_comap_isoObjZero hres hshape T j hj s hpr hmk)
    (fun t _ => support_center_ambientBlowupSeq_subset hres hshape T j hj s hpr hmk t)
    (divisorTransform_succ_eq_strictTransform hres T j hj s hpr hmk)
    (orderAtLeastLocus_inter_divisorTransform_eq_empty hres hfacts T hV hO hD j hj htop hvl s hpr hmk hfin)
    (exists_nonzeroOnComponents_certificate_ambientMarkedSeq hres hfacts hshape T hV hO hD j hj htop hvl s hpr hmk hcert)

private def divisorIdealAfterBlowup (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    ((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr hmk).schemeAt
      (t + 1)).IdealSheafData :=
  AlgebraicGeometry.Scheme.Hom.ker
    (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj
      (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t)

private theorem length_prependedAmbientSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) :
    (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr hmk).length =
      s.length + 1 :=
  congrArg (fun m => m + 1)
    (DivisorReduction.ambientBlowupSeq_length hres blowupPreservesNoetherian T j hj
      (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)

private theorem isoObjZero_prependedAmbientSeq_eq_refl (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) :
    (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr hmk).isoZero =
      Iso.refl T.scheme :=
  BlowupSequenceData.prepend_isoObjZero (DivisorReduction.containedComponentsIdeal T j hj) hb
    (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
      (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)

private theorem center_prependedAmbientSeq_zero (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) :
    (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr hmk).center 0 =
      DivisorReduction.containedComponentsIdeal T j hj :=
  BlowupSequenceData.prepend_center_zero (DivisorReduction.containedComponentsIdeal T j hj) hb
    (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
      (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)

private theorem comap_boundary_isoObjZero_prependedAmbientSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) :
    (T.boundary.get ⟨j, hj⟩).comap
        (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).isoZero.hom = T.boundary.get ⟨j, hj⟩ :=
  (congrArg (fun e => (T.boundary.get ⟨j, hj⟩).comap (Iso.hom e))
      (isoObjZero_prependedAmbientSeq_eq_refl hres T j hj hb s hpr hmk)).trans
    (Scheme.IdealSheafData.comap_id _)

private theorem support_center_zero_prependedAmbientBlowupSeq_subset (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (hV : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) :
    (((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).center 0).support :
        Set ↥((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).schemeAt 0)) ⊆
      ((((T.boundary.get ⟨j, hj⟩).comap
          (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
            hmk).isoZero.hom).support) :
        Set ↥((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).schemeAt 0)) := by
  rw [center_prependedAmbientSeq_zero hres T j hj hb s hpr hmk,
    comap_boundary_isoObjZero_prependedAmbientSeq hres T j hj hb s hpr hmk]
  exact hshape.support_preIdeal_subset_boundary T hV j hj

private theorem isOpen_preimage_support_center_zero_prependedAmbientSeq
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (hV : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) :
    IsOpen (⇑((T.boundary.get ⟨j, hj⟩).comap
        (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).isoZero.hom).subschemeι ⁻¹'
      ((((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).center 0).support) :
        Set ↥((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).schemeAt 0))) := by
  rw [center_prependedAmbientSeq_zero hres T j hj hb s hpr hmk,
    comap_boundary_isoObjZero_prependedAmbientSeq hres T j hj hb s hpr hmk]
  exact hshape.isOpen_preimage_preIdeal T hV j hj

private theorem center_prependedAmbientSeq_succ_eq_imageIdealSheaf (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
        hmk).center (t + 1) =
      imageIdealSheaf (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj
        (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t)
        (s.center t) :=
  DivisorReduction.ambientBlowupSeq_center_eq_imageIdealSheaf hres blowupPreservesNoetherian
    T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t

private theorem support_center_succ_prependedAmbientBlowupSeq_subset (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    (((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).center (t + 1)).support :
        Set ↥((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).schemeAt (t + 1))) ⊆
      ((divisorIdealAfterBlowup hres T j hj hb s hpr hmk t).support :
        Set ↥((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).schemeAt (t + 1))) := by
  have := DivisorReduction.isClosedImmersion_embeddingIntoAmbient hres
    blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
    (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t
  rw [center_prependedAmbientSeq_succ_eq_imageIdealSheaf hres T j hj hb s hpr hmk t]
  exact hshape.support_imageIdeal_subset_ker _ _
    (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj
      (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t)
    (s.center t)

private theorem ker_embeddingIntoAmbient_succ_eq_strictTransform_prepend (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) :
    ∀ t < s.length,
      AlgebraicGeometry.Scheme.Hom.ker
          (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj
            (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr
            (t + 1)) =
        Blowup.strictTransform
          ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
              (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                (DivisorReduction.lowerIdealAfterBlowup T j hj)
                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).map (t + 1))
          ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
              (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                (DivisorReduction.lowerIdealAfterBlowup T j hj)
                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).center (t + 1))
          (AlgebraicGeometry.Scheme.Hom.ker
            (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj
              (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr
              t)) := by
  intro t ht
  rw [BlowupSequenceData.prepend_blowupMorphism_succ, BlowupSequenceData.prepend_center_succ]
  exact ker_embeddingIntoAmbient_succ_eq_strictTransform hres T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
    (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t ht

private theorem prependedDivisorTransform_succ_eq_strictTransform (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) :
    ∀ t < s.length,
      divisorIdealAfterBlowup hres T j hj hb s hpr hmk (t + 1) =
        Blowup.strictTransform
          (((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                  (DivisorReduction.lowerIdealAfterBlowup T j hj)
                  (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).toMarkedBlowupSequenceData
              T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups.transitionMapSucc (t + 1))
          (((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                  (DivisorReduction.lowerIdealAfterBlowup T j hj)
                  (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).toMarkedBlowupSequenceData
              T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups.center (t + 1))
          (divisorIdealAfterBlowup hres T j hj hb s hpr hmk t) := by
  intro t ht
  rw [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism, MarkedBlowupSequenceData.toMarkedSequence_center]
  exact ker_embeddingIntoAmbient_succ_eq_strictTransform_prepend hres T j hj hb s hpr t ht

private theorem isSmoothDivisor_prependedAmbientSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (hV : T.IsAdmissible)
    (hO : T.IsOrderBoundedByMult) (hD : T.IsBalanced hV.locallyOfFiniteType)
    (j : ℕ) (hj : j < T.boundary.length)
    (hne : DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (hvl : (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible)
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) :
    ∀ t ≤ s.length,
      IsSmoothDivisor
        ((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).projectionToSpec (t + 1))
        (divisorIdealAfterBlowup hres T j hj hb s hpr hmk t) :=
  hshape.isSmoothDivisor_ker_pre T hV hO hD j hj hne hb hvl s hpr hmk

private theorem prependedDivisorTransform_zero_eq_comap_blowupMorphism (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) :
    divisorIdealAfterBlowup hres T j hj hb s hpr hmk 0 =
      ((T.boundary.get ⟨j, hj⟩).comap
          (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
            hmk).isoZero.hom).comap
        ((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).transitionMapSucc 0) :=
  hshape.ker_pushedEmb_zero_pre T j hj hb s hpr hmk

private theorem orderAtLeastLocus_inter_prependedDivisorTransform_eq_empty
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (hV : T.IsAdmissible)
    (hO : T.IsOrderBoundedByMult) (hD : T.IsBalanced hV.locallyOfFiniteType)
    (j : ℕ) (hj : j < T.boundary.length)
    (hne : DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (hvl : (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible)
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary)
    (hfin : orderAtLeastLocus (s.ideal s.length) T.mult = ∅) :
    orderAtLeastLocus
        ((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).ideal (s.length + 1)) T.mult ∩
      ((divisorIdealAfterBlowup hres T j hj hb s hpr hmk s.length).support :
        Set ↥((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).schemeAt (s.length + 1))) = ∅ :=
  hfacts.coSupport_inter_ker_eq_empty_pre T hV hO hD j hj hne hb hvl s hpr hfin

private theorem exists_nonzeroOnComponents_certificate_prependedAmbientSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (hV : T.IsAdmissible)
    (hO : T.IsOrderBoundedByMult) (hD : T.IsBalanced hV.locallyOfFiniteType)
    (j : ℕ) (hj : j < T.boundary.length)
    (hne : DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (hvl : (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible)
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary)
    (hcert : ∀ t < s.length,
      PrincipalizationCertificate (s.schemeAt t) (s.projectionToSpec t) (s.ideal t) T.mult (s.boundaryLocus t) (s.center t)) :
    ∀ t < s.length,
      ∃ J : (divisorIdealAfterBlowup hres T j hj hb s hpr hmk t).subscheme.IdealSheafData,
        NonzeroOnComponents J ∧
        (∀ x : ↥(divisorIdealAfterBlowup hres T j hj hb s hpr hmk t).subscheme,
            (divisorIdealAfterBlowup hres T j hj hb s hpr hmk t).subschemeι x ∉
                (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
                  hmk).otherBoundaryLocus j (t + 1) →
              ∃ V : (divisorIdealAfterBlowup hres T j hj hb s hpr hmk t).subscheme.Opens, x ∈ V ∧
                J.comap V.ι =
                  (((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
                      hmk).ideal (t + 1)).comap
                    (divisorIdealAfterBlowup hres T j hj hb s hpr hmk t).subschemeι).comap V.ι) ∧
        PrincipalizationCertificate (divisorIdealAfterBlowup hres T j hj hb s hpr hmk t).subscheme
          ((divisorIdealAfterBlowup hres T j hj hb s hpr hmk t).subschemeι ≫
            (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
              hmk).projectionToSpec (t + 1)) J T.mult
          (⇑(divisorIdealAfterBlowup hres T j hj hb s hpr hmk t).subschemeι ⁻¹'
            (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
              hmk).otherBoundaryLocus j (t + 1))
          (((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
            hmk).center (t + 1)).comap
              (divisorIdealAfterBlowup hres T j hj hb s hpr hmk t).subschemeι) := by
  intro t ht
  have := DivisorReduction.isClosedImmersion_embeddingIntoAmbient hres
    blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
    (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t
  exact exists_principalizationCertificate_ker_of_isClosedImmersion
    (DivisorReduction.embeddingIntoAmbient hres blowupPreservesNoetherian T j hj
      (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t)
    (s.projectionToSpec t)
    ((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
      hmk).projectionToSpec (t + 1))
    (s.ideal t) (s.center t) T.mult (s.boundaryLocus t)
    ((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
      hmk).otherBoundaryLocus j (t + 1))
    ((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
      hmk).ideal (t + 1))
    ((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
      hmk).center (t + 1))
    (hshape.compositeMap_eq_restricted T j hj hb s hpr hmk t)
    (hshape.boundaryLocus_subset_pre T j hj hb s hpr hmk t ht)
    (hfacts.comap_ctrlIdeal_pre T hV hO hD j hj hne hb hvl s hpr t (le_of_lt ht))
    (center_prependedAmbientSeq_succ_eq_imageIdealSheaf hres T j hj hb s hpr hmk t)
    (MarkedSequenceOfBlowups.nonzeroOnComponents_ideal_of_isAdmissible effectiveCartierSupportContainsNoComponent hvl s t (le_of_lt ht))
    (hcert t ht)

private theorem divisorReductionShape_prependedAmbientBlowupSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (hV : T.IsAdmissible)
    (hO : T.IsOrderBoundedByMult) (hD : T.IsBalanced hV.locallyOfFiniteType)
    (j : ℕ) (hj : j < T.boundary.length)
    (hne : DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))
    (hvl : (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible)
    (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s
          hpr)).IsMarked T.structMap T.ideal T.mult T.boundary)
    (hcert : ∀ t < s.length,
      PrincipalizationCertificate (s.schemeAt t) (s.projectionToSpec t) (s.ideal t) T.mult (s.boundaryLocus t) (s.center t))
    (hfin : orderAtLeastLocus (s.ideal s.length) T.mult = ∅) :
    HasSmoothDivisorTransforms T j hj
      (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr hmk) :=
  divisorReductionShape_of_pullback_then_strictTransforms j hj _ s.length (length_prependedAmbientSeq hres T j hj hb s hpr hmk)
    ((T.boundary.get ⟨j, hj⟩).comap
      (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr hmk).isoZero.hom)
    (divisorIdealAfterBlowup hres T j hj hb s hpr hmk)
    (hshape.isSmoothDivisor_boundary_comap T hV j hj
      (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr hmk))
    (isSmoothDivisor_prependedAmbientSeq hres hshape T hV hO hD j hj hne hb hvl s hpr hmk)
    rfl
    (support_center_zero_prependedAmbientBlowupSeq_subset hres hshape T hV j hj hb s hpr hmk)
    (fun t _ => support_center_succ_prependedAmbientBlowupSeq_subset hres hshape T j hj hb s hpr hmk t)
    (isOpen_preimage_support_center_zero_prependedAmbientSeq hres hshape T hV j hj hb s hpr hmk)
    (prependedDivisorTransform_zero_eq_comap_blowupMorphism hres hshape T j hj hb s hpr hmk)
    (prependedDivisorTransform_succ_eq_strictTransform hres T j hj hb s hpr hmk)
    (orderAtLeastLocus_inter_prependedDivisorTransform_eq_empty hres hfacts T hV hO hD j hj hne hb hvl s hpr hmk hfin)
    (exists_nonzeroOnComponents_certificate_prependedAmbientSeq hres hfacts hshape T hV hO hD j hj hne hb hvl s hpr hmk hcert)

theorem exists_smoothDivisorSeq_divisorFamily_canonicalAlgorithmRules
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian)
    (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ) :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.krullDimSucc ≤ n → T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType → ∀ hj : j < T.boundary.length,
        ∃ (D : (t : ℕ) → (((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt t).IdealSheafData)
          (b : Bool),
          (∀ t ≤ ((canonicalAlgorithmRules hres).divisorFamily L j T).length,
              IsSmoothDivisor (((canonicalAlgorithmRules hres).divisorFamily L j T).projectionToSpec t) (D t)) ∧
          D 0 = (T.boundary.get ⟨j, hj⟩).comap
              ((canonicalAlgorithmRules hres).divisorFamily L j T).isoZero.hom ∧
          (∀ t < ((canonicalAlgorithmRules hres).divisorFamily L j T).length,
              ((((canonicalAlgorithmRules hres).divisorFamily L j T).center t).support :
                  Set ↥(((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt t)) ⊆
                ((D t).support : Set ↥(((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt t))) ∧
          (b = true →
            0 < ((canonicalAlgorithmRules hres).divisorFamily L j T).length ∧
            IsOpen (⇑(D 0).subschemeι ⁻¹'
              (((((canonicalAlgorithmRules hres).divisorFamily L j T).center 0).support :
                Set ↥(((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt 0)))) ∧
            D 1 = (D 0).comap (((canonicalAlgorithmRules hres).divisorFamily L j T).transitionMapSucc 0)) ∧
          (∀ t < ((canonicalAlgorithmRules hres).divisorFamily L j T).length, (b = true → t ≠ 0) →
              D (t + 1) =
                Blowup.strictTransform (((canonicalAlgorithmRules hres).divisorFamily L j T).transitionMapSucc t)
                  (((canonicalAlgorithmRules hres).divisorFamily L j T).center t) (D t)) ∧
          (orderAtLeastLocus ((canonicalAlgorithmRules hres).divisorFamily L j T).lastIdeal T.mult ∩
              ((D ((canonicalAlgorithmRules hres).divisorFamily L j T).length).support :
                Set ↥(((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt
                  ((canonicalAlgorithmRules hres).divisorFamily L j T).length)) = ∅) ∧
          (∀ t < ((canonicalAlgorithmRules hres).divisorFamily L j T).length, (b = true → t ≠ 0) →
            ∃ J : (D t).subscheme.IdealSheafData,
              NonzeroOnComponents J ∧
              (∀ x : ↥(D t).subscheme,
                  (D t).subschemeι x ∉
                      ((canonicalAlgorithmRules hres).divisorFamily L j T).otherBoundaryLocus j t →
                    ∃ V : (D t).subscheme.Opens, x ∈ V ∧
                      J.comap V.ι =
                        ((((canonicalAlgorithmRules hres).divisorFamily L j T).ideal t).comap
                          (D t).subschemeι).comap V.ι) ∧
              PrincipalizationCertificate (D t).subscheme
                ((D t).subschemeι ≫ ((canonicalAlgorithmRules hres).divisorFamily L j T).projectionToSpec t) J T.mult
                (⇑(D t).subschemeι ⁻¹'
                  ((canonicalAlgorithmRules hres).divisorFamily L j T).otherBoundaryLocus j t)
                ((((canonicalAlgorithmRules hres).divisorFamily L j T).center t).comap (D t).subschemeι)) := by
  intro T hV hdim hO hD hj
  have hNoe : AlgebraicGeometry.IsNoetherian T.scheme :=
    DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
  show HasSmoothDivisorTransforms T j hj ((canonicalAlgorithmRules hres).divisorFamily L j T)
  rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j T]
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)
  · rw [DivisorReduction.divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian T
      (fun S _ => L S) j hj hcs]
    exact divisorReductionShape_of_orderAtLeastLocus_empty j hj
      (emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary)
      (emptyMarkedSequenceOfBlowups_length T.structMap T.ideal T.mult T.boundary)
      (hshape.isSmoothDivisor_boundary_comap T hV j hj
        (emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary)) hcs
  · have hcoNE : (orderAtLeastLocus T.ideal T.mult).Nonempty := Set.nonempty_iff_ne_empty.mpr hcs
    rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j T hV hj hO hD hcs with
      ⟨htop, hpr, hmk0, heq⟩ | ⟨hne, hb, hpr, hmk0, heq⟩
    · have hvl : (DivisorReduction.restrictToDivisor T j hj).IsAdmissible :=
        hfacts.valid_lowerTop T hV hO hD j hj htop
      have hdimlow : (DivisorReduction.restrictToDivisor T j hj).krullDimSucc < n :=
        lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcoNE j hj
          (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)) hdim
      have hfin : orderAtLeastLocus ((L (DivisorReduction.restrictToDivisor T j hj)).ideal
          (L (DivisorReduction.restrictToDivisor T j hj)).length) T.mult = ∅ := by
        have hr := hL.resolves (DivisorReduction.restrictToDivisor T j hj) hvl hdimlow
        rw [MarkedSequenceOfBlowups.isResolution_iff, MarkedSequenceOfBlowups.lastIdeal_eq] at hr
        exact hr
      rw [heq hmk0]
      exact divisorReductionShape_ambientBlowupSeq hres hfacts hshape T hV hO hD j hj htop hvl
        (L (DivisorReduction.restrictToDivisor T j hj)) hpr hmk0
        (fun t ht => hL.cert (DivisorReduction.restrictToDivisor T j hj) hvl hdimlow t ht) hfin
    · have hvl : (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible :=
        hfacts.valid_lowerPre T hV hO hD j hj hne
      have hdimlow : (DivisorReduction.restrictTwistedToDivisor T j hj).krullDimSucc < n :=
        lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcoNE j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)) hdim
      have hfin : orderAtLeastLocus ((L (DivisorReduction.restrictTwistedToDivisor T j hj)).ideal
          (L (DivisorReduction.restrictTwistedToDivisor T j hj)).length) T.mult = ∅ := by
        have hr := hL.resolves (DivisorReduction.restrictTwistedToDivisor T j hj) hvl hdimlow
        rw [MarkedSequenceOfBlowups.isResolution_iff, MarkedSequenceOfBlowups.lastIdeal_eq] at hr
        exact hr
      rw [heq hmk0]
      exact divisorReductionShape_prependedAmbientBlowupSeq hres hfacts hshape T hV hO hD j hj hne hb hvl
        (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr hmk0
        (fun t ht => hL.cert (DivisorReduction.restrictTwistedToDivisor T j hj) hvl hdimlow t ht) hfin

end FunctorialResolution.EmbeddedResolution

end
