import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StrictPullbackCriterion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCasePrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalizationBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialSplittingFunctoriality
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequenceOfBlowupsPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MapToEarlierScheme
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialBlowupIteration
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BlowupAtMonomialCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenterSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SingleBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace FunctorialResolution.EmbeddedResolution

def OrderAtBaseFieldChangeInvariance : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base)),
      b ≫ T.structMap = pB →
      ∀ (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
        (@MarkedIdealWithBoundary.mk T.base T.instField B pB IB T.mult EB).IsAdmissible →
        ∀ (Q : Scheme.{u}) (a : Q ⟶ B)
          (b' : Q ⟶ pullback T.structMap (specMapOfFieldHom T.base L f)),
          IsPullback a b' b (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) →
          ∀ (A : B.IdealSheafData) (y : ↥Q), orderAt (A.comap a) y = orderAt A (a y)

instance instSurjectivePullbackFstSpecMapField (k L : Type u) [Field k] [Field L]
    (f : k →+* L) (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k)) :
    AlgebraicGeometry.Surjective (pullback.fst p (specMapOfFieldHom k L f)) :=
  inferInstance

private theorem isPullbackBlowupSequence_monomialPrincipalization_baseChange (hGeom : MonomialGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u})
    (hord : OrderAtBaseFieldChangeInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : MonomialCenter.IsLocallyMonomialTriple T) (L : Type u) [Field L] [CharZero L]
    (f : T.base →+* L) (E' : List (T.baseChange L f).scheme.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E')
    (hT' : MonomialCenter.IsLocallyMonomialTriple ((T.baseChange L f).withBoundary E')) :
    IsPullbackBlowupSequence (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
      (monomialPrincipalization hinv ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups
      (monomialPrincipalization hinv T).toSequenceOfBlowups := by
  have : AlgebraicGeometry.Flat (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    inferInstance
  have hord' : ∀ (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base)),
      b ≫ T.structMap = pB →
      ∀ (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
        (@MarkedIdealWithBoundary.mk T.base T.instField B pB IB T.mult EB).IsAdmissible →
        ∀ (Q : Scheme.{u}) (a : Q ⟶ B)
          (b' : Q ⟶ pullback T.structMap (specMapOfFieldHom T.base L f)),
          IsPullback a b' b (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) →
          ∀ (A : B.IdealSheafData) (z : ↥Q), orderAt (A.comap a) z = orderAt A (a z) :=
    hord T hT.valid L f
  exact monomialPrincipalization_isPullbackBlowupSequence_of_flat hGeom hinv T
    (pullback T.structMap (specMapOfFieldHom T.base L f)) L
    (pullback.snd T.structMap (specMapOfFieldHom T.base L f))
    (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) E' hT hE.symm hT' hord'

theorem isLocallyMonomialPrincipalization_monomialPrincipalization
    (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (hord : OrderAtBaseFieldChangeInvariance.{u}) (P : ℕ → Prop) :
    MonomialCenter.IsLocallyMonomialPrincipalization P (monomialPrincipalization hinv) := by
  have hmonomial := isMonomialCasePrincipalization_monomialPrincipalization hGeom hinv
  have hne : ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
      ∀ i : ℕ, i < (monomialPrincipalization hinv T).length →
        (monomialPrincipalization hinv T).center i ≠ ⊤ := fun T hT i hi =>
    (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mp
      (monomialPrincipalization_center_support_nonempty hGeom hinv T hT i hi)
  refine
    { center_subset_boundaryLocus := fun T hT _ => hmonomial.center_subset_boundaryLocus T hT
      cert := fun T hT _ => hmonomial.cert T hT
      base_change := ?_
      base_change_strict := ?_
      center_eq := fun T hT _ => hmonomial.center_eq T hT
      minLevel_ne_zero := fun T hT _ => hmonomial.minLevel_ne_zero T hT
      key_le := fun T hT _ => hmonomial.key_le T hT
      monomial_near := fun T hT _ => hmonomial.monomial_near T hT
      center_nonempty := fun T hT _ => hmonomial.center_nonempty T hT
      resolves := fun T hT _ => hmonomial.resolves T hT
      smooth_pullback := ?_
      smooth_pullback_strict := ?_
      trivial_of_coSupport_empty := fun T hT _ => hmonomial.trivial_of_coSupport_empty T hT }
  · intro T hT _ L instL instCZ f E' hE hT' _
    exact isPullbackBlowupSequence_monomialPrincipalization_baseChange hGeom hinv hord T hT L f E' hE hT'
  · intro T hT _ L instL instCZ f E' hE hT' _
    exact (isPullbackBlowupSequence_monomialPrincipalization_baseChange hGeom hinv hord T hT L f E' hE
      hT').isStrictPullback_of_surjective (hne T hT)
  · intro T hT _ Y q h hsmooth hq E' hE hT' _
    exact monomialPrincipalization_isPullbackBlowupSequence_of_smooth hGeom hinv T hT Y q h hq E' hE hT'
  · intro T hT _ Y q h hsmooth instSurj hq E' hE hT' _
    exact (monomialPrincipalization_isPullbackBlowupSequence_of_smooth hGeom hinv T hT Y q h hq E' hE
      hT').isStrictPullback_of_surjective (hne T hT)

end FunctorialResolution.EmbeddedResolution
