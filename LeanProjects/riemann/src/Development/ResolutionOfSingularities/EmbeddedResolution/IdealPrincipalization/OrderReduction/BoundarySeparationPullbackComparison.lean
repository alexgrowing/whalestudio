import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.DisjointCentersPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequenceOfBlowupsPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupSeqComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparation
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparationBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TrivialDivisorContinuation
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.ContinuationComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.SameNontrivialBoundary
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

namespace NontrivialBoundary

theorem nonempty_separateBoundaryPullbackComparison
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (Bl : PrincipalizationAssignment.{u})
    (hspec : ∀ i : ℕ, IsBoundaryDivisorReduction P i (A i) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (T : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [AlgebraicGeometry.Smooth q]
    (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hdim' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).krullDimSucc ≤ T.krullDimSucc)
    (j : ℕ) (hj : j ≤ S.boundary.length) :
    Nonempty (SequenceOfBlowupsPullback q
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.survivingBoundaryCount S q j)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  classical
  have : AlgebraicGeometry.Flat q := inferInstance
  revert hj
  induction j with
  | zero =>
    intro _
    have e0 : BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S 0
        = FunctorialResolution.EmbeddedResolution.emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary :=
      MaxContactCoverData.separateBoundary_zero hinv T (fun S₀ _ i => A i S₀) S
    have e0' : BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.survivingBoundaryCount S q 0)
        = FunctorialResolution.EmbeddedResolution.emptyMarkedBlowupSequenceData (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap
            (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal (NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult
            (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary := by
      rw [NontrivialBoundary.survivingBoundaryCount_zero]
      exact MaxContactCoverData.separateBoundary_zero hinv T (fun S₀ _ i => A i S₀)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
    rw [e0, e0']
    simp only [FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups]
    refine ⟨SequenceOfBlowupsPullback.ofCentersMissImage q _ ?_ _ ?_⟩
    · intro i hi
      simp at hi
    · simp
  | succ j ih =>
    intro hj1
    have hjS : j < S.boundary.length := Nat.lt_of_succ_le hj1
    obtain ⟨D⟩ := ih (Nat.le_of_succ_le hj1)
    have hftS : AlgebraicGeometry.LocallyOfFiniteType
        ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).proj
            (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).length ≫ S.structMap) :=
      BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar S hV _ _ le_rfl
    have hftT : AlgebraicGeometry.LocallyOfFiniteType
        ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
              (NontrivialBoundary.survivingBoundaryCount S q j)).proj
            (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
              (NontrivialBoundary.survivingBoundaryCount S q j)).length
          ≫ (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap) :=
      BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV'
        _ _ le_rfl
    have hm : 1 ≤ S.mult := hV.one_le_mult
    have hdimU : (MaxContactCoverData.derivedTriple S
          (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j) hftS [] 0).krullDimSucc ≤ T.krullDimSucc :=
      hstar.derivedTriple_dim_le (T := T) hV (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j) hftS [] 0 hdimS
    have hPU :
        P (MaxContactCoverData.derivedTriple S (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j) hftS [] 0).krullDimSucc :=
      hmono _ _ hdimU hPdimT
    have hVU := BoundarySeparationBaseChange.isAdmissible_derivedTriple_nil hstar S hV
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j) hftS
    have hdimU' : (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
            (NontrivialBoundary.survivingBoundaryCount S q j)) hftT [] 0).krullDimSucc ≤ T.krullDimSucc :=
      hstar.derivedTriple_dim_le (T := T) hV'
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.survivingBoundaryCount S q j))
        hftT [] 0 hdim'
    have hPU' : P (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
            (NontrivialBoundary.survivingBoundaryCount S q j)) hftT [] 0).krullDimSucc :=
      hmono _ _ hdimU' hPdimT
    have hVU' := BoundarySeparationBaseChange.isAdmissible_derivedTriple_nil hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV'
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.survivingBoundaryCount S q j))
      hftT
    have hO' : ∀ x : ↥(NontrivialBoundary.pullbackWithNontrivialBoundary S q).scheme,
        orderAt (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal x ≤ ((S.mult : ℕ) : ℕ∞) :=
      fun x => BoundarySeparationBaseChange.orderAt_pullbackTriple_le_mult S q hV hO x
    have eS : BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S (j + 1)
        = MaxContactReduction.appendLowerDimReduction hinv T (fun S₀ _ i => A i S₀) S
            (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j) [] 0 j :=
      MaxContactCoverData.separateBoundary_succ hinv T (fun S₀ _ i => A i S₀) S j
    by_cases hlive : (S.boundary[j]'hjS).comap q = ⊤
    · have eT : NontrivialBoundary.survivingBoundaryCount S q (j + 1) = NontrivialBoundary.survivingBoundaryCount S q j :=
        NontrivialBoundary.survivingBoundaryCount_succ_of_eq_top S q j hjS hlive
      rw [eS, eT]
      have hjlen : j < ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).boundary
          (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).length).length :=
        lt_of_lt_of_le hjS
          (NontrivialBoundary.length_boundary_le_length_lastBoundary S (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j))
      have hBoundaryTop : (((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).boundary
              (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).length).get ⟨j, hjlen⟩).comap D.lastMap
          = ⊤ := by
        rw [List.get_eq_getElem]
        exact NontrivialBoundary.lastBoundary_comap_lastMap_eq_top S q
          (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j)
          (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
            (NontrivialBoundary.survivingBoundaryCount S q j)) D hstar hV hV' j hjS hlive
      exact TrivialDivisorContinuation.nonempty_pullback_appendLowerDimReduction_of_comap_eq_top P A Bl j S q
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j)
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.survivingBoundaryCount S q j))
        D hftS hstar (hspec j) hV hm hO hPU hVU hjlen hBoundaryTop hinv T hdimU
    · have eT : BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
            (NontrivialBoundary.survivingBoundaryCount S q (j + 1))
          = MaxContactReduction.appendLowerDimReduction hinv T (fun S₀ _ i => A i S₀) (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
              (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
                (NontrivialBoundary.survivingBoundaryCount S q j)) [] 0 (NontrivialBoundary.survivingBoundaryCount S q j) := by
        rw [NontrivialBoundary.survivingBoundaryCount_succ_of_ne_top S q j hjS hlive]
        exact MaxContactCoverData.separateBoundary_succ hinv T (fun S₀ _ i => A i S₀)
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q) (NontrivialBoundary.survivingBoundaryCount S q j)
      rw [eS, eT]
      exact ⟨BoundaryDeletion.continuationComparison (P := P) (A := A) (Bl := Bl) (j := j) (S := S)
        (q := q) (s := BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j)
        (s' := BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.survivingBoundaryCount S q j))
        (Dt := D) (hftS := hftS) (hftT := hftT) (hinv := hinv) (T := T)
        (hstar := hstar) (hspec := hspec j) (hspec' := hspec (NontrivialBoundary.survivingBoundaryCount S q j))
        (hshift := hshift) (hV := hV) (hV' := hV') (hm := hm) (hO := hO) (hO' := hO')
        (hj := hjS) (hlive := hlive) (hPU := hPU) (hVU := hVU) (hPU' := hPU') (hVU' := hVU')
        (hdimU := hdimU) (hdimU' := hdimU')⟩

def separateBoundaryPullbackComparison
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (Bl : PrincipalizationAssignment.{u})
    (hspec : ∀ i : ℕ, IsBoundaryDivisorReduction P i (A i) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (T : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [AlgebraicGeometry.Smooth q]
    (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hdim' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).krullDimSucc ≤ T.krullDimSucc)
    (j : ℕ) (hj : j ≤ S.boundary.length) :
    SequenceOfBlowupsPullback q
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.survivingBoundaryCount S q j)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
  (nonempty_separateBoundaryPullbackComparison P hmono A Bl hspec hshift hstar hinv T hPdimT S q hV hO hdimS hV' hdim'
    j hj).some

end NontrivialBoundary

end FunctorialResolution.EmbeddedResolution

end
