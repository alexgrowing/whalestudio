import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedPullbackSquare
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialSplittingFunctoriality
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderPullbackInvariance
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalizationBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MarkedPullbackSquare

variable {T : MarkedIdealWithBoundary.{u}} {Y : Scheme.{u}} {g : Y ⟶ T.scheme}

theorem smooth_verticalMap (S : MarkedPullbackSquare T g) [AlgebraicGeometry.Smooth g] :
    AlgebraicGeometry.Smooth S.left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Smooth) S.isPullback.flip ‹AlgebraicGeometry.Smooth g›

theorem verticalMap_comp_lowerStructMap (S : MarkedPullbackSquare T g) (q : Y ⟶ Spec (CommRingCat.of T.base))
    (hq : g ≫ T.structMap = q) :
    S.left ≫ S.structMap = S.top ≫ q := by
  rw [← S.bottom_structMap, ← hq, ← Category.assoc, S.isPullback.w, Category.assoc]

theorem pullbackOverField_isAdmissible_of_sameNontrivialBoundary (hGeom : MonomialGeometryHypotheses.{u}) (S : MarkedPullbackSquare T g)
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (E : List S.topScheme.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (List.map (fun D => D.comap S.left) S.boundary) E)
    (hV : (S.upperTriple k' q E).IsAdmissible) :
    (S.lowerTriple.pullbackOverField S.topScheme k' (S.top ≫ q) S.left).IsAdmissible :=
  hGeom.withBoundary_valid (S.upperTriple k' q E) hV
    ((S.lowerTriple.pullbackOverField S.topScheme k' (S.top ≫ q) S.left).boundary) hE.symm

theorem orderAt_comap_verticalMap_le_of_forall_orderAt_le (S : MarkedPullbackSquare T g) (hT : T.IsAdmissible)
    (hg : OrderAtPullbackInvariant T g)
    (hord : ∀ x : ↥S.baseScheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) (y : ↥S.topScheme) :
    orderAt (S.ideal.comap S.left) y ≤ (S.mult : ℕ∞) :=
  S.orderAt_comap_verticalMap_le hT hg S.ideal _ hord y

end MarkedPullbackSquare

theorem baseChangeCompatible_of_smooth (hG : PrincipalizationGeometryHypotheses.{u}) (τ : ComapIsoInvariance.{u}) (n : ℕ)
    (F G : PrincipalizationAssignment.{u}) (hF : IsOrderReduction (fun d => d ≤ n) F G)
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) {Y : Scheme.{u}}
    (g : Y ⟶ T.scheme) [AlgebraicGeometry.Smooth g]
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (hq : g ≫ T.structMap = q) :
    BaseChangeCompatible τ F n T g T.base q := by
  have hgord : OrderAtPullbackInvariant T g := orderAtPullbackInvariant_of_smooth T hT g
  refine ⟨?_, ?_, ?_, ?_, hgord⟩
  · intro S hord E hE hV hdimS
    have : AlgebraicGeometry.Smooth S.left := MarkedPullbackSquare.smooth_verticalMap S
    exact hF.smooth_pullback S.lowerTriple S.valid (le_trans S.dim_le hdim) hord S.topScheme
      (S.top ≫ q) S.left (MarkedPullbackSquare.verticalMap_comp_lowerStructMap S q hq) E hE hV hdimS
      (fun y => MarkedPullbackSquare.orderAt_comap_verticalMap_le_of_forall_orderAt_le S hT hgord hord y)
  · exact inferInstance
  · intro S hmon E hE hmon'
    have : AlgebraicGeometry.Smooth S.left := MarkedPullbackSquare.smooth_verticalMap S
    exact monomialPrincipalization_isPullbackBlowupSequence_of_smooth hG.monomialInputs τ S.lowerTriple hmon
      S.topScheme (S.top ≫ q) S.left (MarkedPullbackSquare.verticalMap_comp_lowerStructMap S q hq) E hE hmon'
  · intro S E hE hV
    have : AlgebraicGeometry.Smooth S.left := MarkedPullbackSquare.smooth_verticalMap S
    exact hG.nonMonomialPart_comap_of_sameNontrivialBoundary S.lowerTriple S.valid S.topScheme
      (S.top ≫ q) S.left (MarkedPullbackSquare.verticalMap_comp_lowerStructMap S q hq)
      (MarkedPullbackSquare.pullbackOverField_isAdmissible_of_sameNontrivialBoundary hG.monomialInputs S T.base q E hE hV)
      E hE hV

end FunctorialResolution.EmbeddedResolution

end
