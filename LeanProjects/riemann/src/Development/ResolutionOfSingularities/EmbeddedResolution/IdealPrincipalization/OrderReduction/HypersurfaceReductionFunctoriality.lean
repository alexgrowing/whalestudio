import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparation
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverTriple
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.FaithfullyFlatDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparationBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparationPullbackComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LowerDimensionalContinuation
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.SameNontrivialBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactHypersurfaceTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactFunctoriality

theorem isPullbackBlowupSequence_reduceAlongHypersurface_of_smooth
    (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (Bl : PrincipalizationAssignment.{u})
    (hspec : ∀ i : ℕ, IsBoundaryDivisorReduction P i (A i) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (T : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (H : S.scheme.IdealSheafData)
    (hH : ∀ [AlgebraicGeometry.LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [AlgebraicGeometry.Smooth q]
    (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hdim' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).krullDimSucc ≤ T.krullDimSucc)
    (hH' : ∀ [AlgebraicGeometry.LocallyOfFiniteType (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap],
      IsMaxContactHypersurface (NontrivialBoundary.pullbackWithNontrivialBoundary S q).base
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult (H.comap q))
    (hH'snc : InStrictNormalCrossingPosition (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap [H.comap q]) :
    IsPullbackBlowupSequence q
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S₀ _ i => A i S₀)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q) (H.comap q)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S₀ _ i => A i S₀) S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have hcnt : NontrivialBoundary.survivingBoundaryCount S q S.boundary.length
      = (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length := NontrivialBoundary.survivingBoundaryCount_length_eq S q
  have Dt0 := NontrivialBoundary.separateBoundaryPullbackComparison P hmono A Bl hspec hshift hstar hinv T hPdimT S q hV hO
    hdimS hV' hdim' S.boundary.length le_rfl
  rw [hcnt] at Dt0
  have hftS : AlgebraicGeometry.LocallyOfFiniteType
      ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length).proj
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length).length ≫ S.structMap) :=
    BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar S hV _ _ le_rfl
  have hftT : AlgebraicGeometry.LocallyOfFiniteType
      ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).proj
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).length
        ≫ (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap) :=
    BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' _ _
      le_rfl
  have hF := BoundarySeparationBaseChange.separateBoundaryInvariant_separateBoundaryOfFamily hstar hinv P hmono A Bl hspec T hPdimT S
    hV hO hdimS H hHsnc S.boundary.length le_rfl
  have hF' := BoundarySeparationBaseChange.separateBoundaryInvariant_separateBoundaryOfFamily hstar hinv P hmono A Bl hspec T hPdimT
    (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' (BoundarySeparationBaseChange.orderAt_pullbackTriple_le_mult S q hV hO) hdim' (H.comap q)
    hH'snc (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length le_rfl
  have hm : 1 ≤ S.mult := hV.one_le_mult
  have hO' : ∀ x : ↥(NontrivialBoundary.pullbackWithNontrivialBoundary S q).scheme,
      orderAt (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal x ≤ ((S.mult : ℕ) : ℕ∞) :=
    BoundarySeparationBaseChange.orderAt_pullbackTriple_le_mult S q hV hO
  have hdimU : (MaxContactCoverData.derivedTriple S
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) hftS
      [MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) H]
      S.boundary.length).krullDimSucc ≤ T.krullDimSucc :=
    hstar.derivedTriple_dim_le hV _ hftS _ _ hdimS
  have hPU : P (MaxContactCoverData.derivedTriple S
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) hftS
      [MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) H]
      S.boundary.length).krullDimSucc := hmono _ _ hdimU hPdimT
  have hsncU : InStrictNormalCrossingPosition
      ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length).proj
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length).length ≫ S.structMap)
      ([MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) H] ++
        List.drop S.boundary.length
          ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length).boundary
            (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length).length)) := by
    simpa [MaxContactReduction.strictTransformAtLength_eq] using
      inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar S hV hO H (@hH hV.locallyOfFiniteType)
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) hF.2.2 _ le_rfl
  have hVU := BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar S hV
    (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) hftS
    [MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) H]
    S.boundary.length hsncU
  have hdimU' : (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) hftT
      [MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) (H.comap q)]
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).krullDimSucc ≤ T.krullDimSucc :=
    hstar.derivedTriple_dim_le hV' _ hftT _ _ hdim'
  have hPU' : P (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) hftT
      [MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) (H.comap q)]
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).krullDimSucc := hmono _ _ hdimU' hPdimT
  have hsncU' : InStrictNormalCrossingPosition
      ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).proj
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).length
        ≫ (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap)
      ([MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) (H.comap q)] ++
        List.drop (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length
          ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
            (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).boundary
            (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
              (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).length)) := by
    simpa [MaxContactReduction.strictTransformAtLength_eq] using
      inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV'
        (BoundarySeparationBaseChange.orderAt_pullbackTriple_le_mult S q hV hO) (H.comap q) (@hH' hV'.locallyOfFiniteType)
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) hF'.2.2 _ le_rfl
  have hVU' := BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV'
    (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) hftT
    [MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) (H.comap q)]
    (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length hsncU'
  have hsep : BoundarySeparationByMaxContact.BoundarySeparated S
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) S.boundary.length := hF.1
  have hsep' : BoundarySeparationByMaxContact.BoundarySeparated (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length)
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length := hF'.1
  simp only [MaxContactCoverData.reduceAlongHypersurface_eq_appendLowerDimReduction]
  exact StrictTransformComparison.isPullbackBlowupSequence_appendLowerDimReduction (P := P) (A := A) (Bl := Bl) (S := S) (q := q)
    (s := BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length)
    (s' := BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length)
    (Dt := Dt0) (hftS := hftS) (hftT := hftT) (hinv := hinv) (T := T) (hstar := hstar)
    (hspec := hspec 0) (H := H) (hV := hV) (hV' := hV') (hm := hm) (hO := hO) (hO' := hO')
    (hdimU := hdimU) (hPU := hPU) (hVU := hVU) (hdimU' := hdimU') (hPU' := hPU') (hVU' := hVU')
    (hsep := hsep) (hsep' := hsep')

theorem isPullbackBlowupSequence_reduceAlongHypersurface_lowerDimensionalFamily
    (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u})
    (_hin : _root_.FunctorialResolution.EmbeddedResolution.OrderReduction.OrderReductionHypotheses)
    (_hMC : _root_.FunctorialResolution.EmbeddedResolution.BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u})
    (_hAdm : _root_.FunctorialResolution.EmbeddedResolution.BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u})
    (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (Bl : PrincipalizationAssignment.{u})
    (hspec : ∀ i : ℕ, IsBoundaryDivisorReduction P i (A i) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (T T' : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc) (hPdimOther : P T'.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (_hBoundaryNeTop : ∀ D ∈ S.boundary, D ≠ ⊤)
    (H : S.scheme.IdealSheafData)
    (hH : ∀ [AlgebraicGeometry.LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [AlgebraicGeometry.Smooth q]
    (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hdim' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).krullDimSucc ≤ T'.krullDimSucc)
    (hH' : ∀ [AlgebraicGeometry.LocallyOfFiniteType (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap],
      IsMaxContactHypersurface (NontrivialBoundary.pullbackWithNontrivialBoundary S q).base
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult (H.comap q))
    (hH'snc : InStrictNormalCrossingPosition (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap [H.comap q]) :
    IsPullbackBlowupSequence q
      (MaxContactReduction.reduceAlongHypersurface hinv T' (lowerDimensionalFamily A T')
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q) (H.comap q)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.reduceAlongHypersurface hinv T (lowerDimensionalFamily A T) S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  rcases le_total T.krullDimSucc T'.krullDimSucc with hle | hle
  · rw [reduceAlongHypersurface_congr_of_dim_le hstar hinv A T T' hle S hV hdimS H]
    exact isPullbackBlowupSequence_reduceAlongHypersurface_of_smooth hstar hinv P hmono A Bl hspec hshift T' hPdimOther S hV hO
      (le_trans hdimS hle) H hH hHsnc q hV' hdim' hH' hH'snc
  · rw [reduceAlongHypersurface_congr_of_dim_le hstar hinv A T' T hle (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' hdim'
      (H.comap q)]
    exact isPullbackBlowupSequence_reduceAlongHypersurface_of_smooth hstar hinv P hmono A Bl hspec hshift T hPdimT S hV hO hdimS
      H hH hHsnc q hV' (le_trans hdim' hle) hH' hH'snc

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution

end
