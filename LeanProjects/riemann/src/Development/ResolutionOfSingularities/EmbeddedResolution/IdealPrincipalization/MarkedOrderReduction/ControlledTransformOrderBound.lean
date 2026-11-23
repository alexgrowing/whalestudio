import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupClosedSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.ControlledTransformOrderBound
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem orderAt_controlledTransform_le_of_orderAt_eq_on_center :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ (J : T.scheme.IdealSheafData) (c : ℕ),
                (∀ x ∈ Z.support, orderAt J x = (c : ℕ∞)) →
                  ∀ (J' : X'.IdealSheafData),
                    Blowup.exceptionalIdeal π Z ^ c * J' = J.comap π →
                      ∀ x' ∈ (Blowup.exceptionalIdeal π Z).support, orderAt J' x' ≤ (c : ℕ∞) := by
  intro T hT Z hZsm hZsnc X' π hπ J c hJ J' hJ' x' hx'
  have : CharZero T.base := hT.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hT.smooth
  have hN : AlgebraicGeometry.IsNoetherian T.scheme := hT.isNoetherian
  have hlocNoeth : AlgebraicGeometry.IsLocallyNoetherian T.scheme := inferInstance
  have hLN' : AlgebraicGeometry.IsLocallyNoetherian X' :=
    isLocallyNoetherian_of_isBlowupAlongIdealSheaf π Z hπ
  have hsub : (Z.support : Set ↥T.scheme) ⊆ orderAtLeastLocus J c := by
    intro x hx
    exact (mem_orderAtLeastLocus_iff J c x).2 (hJ x hx).ge
  have hI : J ≤ Z ^ c :=
    le_pow_of_hasStrictNormalCrossingsWith T.structMap Z J T.boundary hZsnc c hsub
  have hJ'eq : J' = controlledTransform π Z J c hπ hI :=
    eq_controlledTransform_of_mul_eq_comap π Z J c hπ hI J' hJ'
  rw [hJ'eq]
  refine orderAt_controlledTransform_le_of_orderAt_image_le T.base T.structMap π Z T.boundary
    hZsnc hπ J c hI x' ?_
  have h1 : π x' ∈ (Z.support : Set ↥T.scheme) :=
    AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.1
      (by rw [← Blowup.exceptionalIdeal_eq_comap π Z]; exact hx')
  exact le_of_eq (hJ _ h1)

structure StrictTransformAndMonomialCaseHypotheses : Prop where
  strictTransform_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ D ∈ T.boundary,
                ∀ C' : Set ↥X',
                  IsIrreducibleComponentOf C' ((Blowup.strictTransform π Z D).support : Set ↥X') →
                    ∃ (ξ' : ↥X') (C : Set ↥T.scheme),
                      C' = closure ({ξ'} : Set ↥X') ∧
                        ξ' ∉ (Blowup.exceptionalIdeal π Z).support ∧
                          IsIrreducibleComponentOf C (D.support : Set ↥T.scheme) ∧
                            ¬ C ⊆ (Z.support : Set ↥T.scheme) ∧
                              C = closure ({π ξ'} : Set ↥T.scheme)
  monomial : MonomialCaseHypotheses.{u}

theorem OrderReductionHypotheses.of_strictTransformHypotheses (h : StrictTransformAndMonomialCaseHypotheses.{u}) :
    OrderReductionHypotheses.{u} where
  controlledTransform_orderAt_le := orderAt_controlledTransform_le_of_orderAt_eq_on_center
  strictTransform_components := h.strictTransform_components
  monomial := h.monomial

end FunctorialResolution.EmbeddedResolution

end
