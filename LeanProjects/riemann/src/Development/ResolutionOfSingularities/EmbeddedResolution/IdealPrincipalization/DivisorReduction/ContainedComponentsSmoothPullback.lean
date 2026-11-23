import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.DimensionNonincreasing
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

theorem smooth_of_isPullback (X Y S S' : Scheme.{u}) (σ : S ⟶ X) (σ' : S' ⟶ Y) (φ : Y ⟶ X)
    (ψ : S' ⟶ S) (hpb : IsPullback σ' ψ φ σ) (hφ : AlgebraicGeometry.Smooth φ) :
    AlgebraicGeometry.Smooth ψ :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Smooth) hpb hφ

theorem orderAtLeastLocus_comap_of_smooth (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) [AlgebraicGeometry.Smooth h]
    (_hq : h ≫ T.structMap = q) (m : ℕ) :
    orderAtLeastLocus (T.ideal.comap h) m = ⇑h ⁻¹' orderAtLeastLocus T.ideal m := by
  have : CharZero T.base := hV.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  exact FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_comap T.base T.structMap h T.ideal m

private theorem withBoundary_withBoundary (T : MarkedIdealWithBoundary.{u})
    (E F : List T.scheme.IdealSheafData) :
    (T.withBoundary E).withBoundary F = T.withBoundary F := rfl

private theorem isAdmissible_of_withBoundary_isAdmissible (S : MarkedIdealWithBoundary.{u})
    (E : List S.scheme.IdealSheafData) (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary S.boundary E)
    (hV : (S.withBoundary E).IsAdmissible) : S.IsAdmissible := by
  have h1 : ((S.withBoundary E).withBoundary S.boundary).IsAdmissible :=
    MarkedIdealWithBoundary.validOfSameNontrivialBoundary _ _ hV hBE.symm
  rw [withBoundary_withBoundary, MarkedIdealWithBoundary.withBoundary_self] at h1
  exact h1

theorem isAdmissible_pullbackAlong_of_withBoundary_isAdmissible :
    ∀ (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base))
      (h : Y ⟶ T.scheme) (E' : List Y.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
        ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible → (T.pullbackAlong Y q h).IsAdmissible := by
  intro T Y q h E' hBE hV
  exact isAdmissible_of_withBoundary_isAdmissible (T.pullbackAlong Y q h) E' hBE hV

theorem containedComponentsIdeal_pullbackAlong_of_isAdmissible_pullbackAlong
    {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}} {hno : BlowupPreservesNoetherian.{u}}
    (hfacts : DivisorReductionTerminationProperties hres hno)
    (hvbr : ∀ (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base))
      (h : Y ⟶ T.scheme) (E' : List Y.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
        ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible → (T.pullbackAlong Y q h).IsAdmissible) :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
          ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
            List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary →
            ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
              containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE =
                (containedComponentsIdeal T j hj).comap h := by
  intro T hV Y q h hsm hq E' hBE j hj hjE htake hV'
  have : AlgebraicGeometry.Smooth h := hsm
  have hj' : j < (T.pullbackAlong Y q h).boundary.length := by
    simpa [MarkedIdealWithBoundary.pullbackAlong_boundary] using hj
  have hVal : (T.pullbackAlong Y q h).IsAdmissible := hvbr T Y q h E' hBE hV'
  rw [containedComponentsIdeal_withBoundary T j Y q h E' hjE hj' htake]
  exact hfacts.preIdeal_pullbackAlong T hV Y q h hq hVal j hj hj'

theorem containedComponentsIdeal_pullbackAlong_of_smooth {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} (hfacts : DivisorReductionTerminationProperties hres hno) :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
          ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
            List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary →
            ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
              containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE =
                (containedComponentsIdeal T j hj).comap h :=
  containedComponentsIdeal_pullbackAlong_of_isAdmissible_pullbackAlong hfacts
    isAdmissible_pullbackAlong_of_withBoundary_isAdmissible

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
