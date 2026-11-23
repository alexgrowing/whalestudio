import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequencePrefix
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequenceOfBlowupsPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.BlowupDataOfSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparation
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverTriple
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.IteratedStrictTransformPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparationBaseChange
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

namespace StrictTransformComparison

variable (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u}) (Bl : PrincipalizationAssignment.{u})
  (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [AlgebraicGeometry.Smooth q]
  (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
  (s' : MarkedBlowupSequenceData (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary)
  (Dt : SequenceOfBlowupsPullback q s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
  (hftS : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
  (hftT : AlgebraicGeometry.LocallyOfFiniteType
    (s'.proj s'.length ≫ (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap))

theorem strictTransformAtLength_comap_lastMap
    (hstar : MaxContactCoverProperties.{u})
    (hV : S.IsAdmissible) (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (H : S.scheme.IdealSheafData) :
    MaxContactReduction.strictTransformAtLength s' (H.comap q)
      = (MaxContactReduction.strictTransformAtLength s H).comap Dt.lastMap := by
  have : AlgebraicGeometry.Flat q := inferInstance
  have h1 : MaxContactReduction.strictTransformAtLength s' (H.comap q) = s'.iteratedStrictTransform s'.length (H.comap q) := by
    rw [MaxContactReduction.strictTransformAtLength_eq, BoundarySeparationByMaxContact.iteratedStrictTransform_eq_toBlowupSequenceData]
  have h2 : MaxContactReduction.strictTransformAtLength s H = s.iteratedStrictTransform s.length H := by
    rw [MaxContactReduction.strictTransformAtLength_eq, BoundarySeparationByMaxContact.iteratedStrictTransform_eq_toBlowupSequenceData]
  rw [h1, h2]
  exact (NontrivialBoundary.iteratedStrictTransform_comap_lastMap S q s s' Dt hstar hV hV' H).symm

include Dt in
theorem isPullbackBlowupSequence_appendLowerDimReduction
    (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (hstar : MaxContactCoverProperties.{u})
    (hspec : IsBoundaryDivisorReduction P 0 (A 0) Bl)
    (H : S.scheme.IdealSheafData)
    (hV : S.IsAdmissible) (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hm : 1 ≤ S.mult)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ ((S.mult : ℕ) : ℕ∞))
    (hO' : ∀ x : ↥(NontrivialBoundary.pullbackWithNontrivialBoundary S q).scheme,
      orderAt (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal x ≤ ((S.mult : ℕ) : ℕ∞))
    (hdimU : (MaxContactCoverData.derivedTriple S s hftS
        [MaxContactReduction.strictTransformAtLength s H] S.boundary.length).krullDimSucc ≤ T.krullDimSucc)
    (hPU : P (MaxContactCoverData.derivedTriple S s hftS
        [MaxContactReduction.strictTransformAtLength s H] S.boundary.length).krullDimSucc)
    (hVU : (MaxContactCoverData.derivedTriple S s hftS
        [MaxContactReduction.strictTransformAtLength s H] S.boundary.length).IsAdmissible)
    (hdimU' : (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).krullDimSucc ≤ T.krullDimSucc)
    (hPU' : P (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).krullDimSucc)
    (hVU' : (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).IsAdmissible)
    (hsep : BoundarySeparationByMaxContact.BoundarySeparated S s S.boundary.length)
    (hsep' : BoundarySeparationByMaxContact.BoundarySeparated (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s'
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) :
    IsPullbackBlowupSequence q
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S₀ _ i => A i S₀) (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s'
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length 0).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S₀ _ i => A i S₀) S s
        [MaxContactReduction.strictTransformAtLength s H] S.boundary.length 0).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have : AlgebraicGeometry.Flat q := inferInstance
  have hSmoothLast : AlgebraicGeometry.Smooth Dt.lastMap := SequenceOfBlowupsPullback.smooth_lastMap Dt
  have hsm : AlgebraicGeometry.Smooth (s.proj s.length ≫ S.structMap) :=
    BoundarySeparationByMaxContact.smooth_projectionToBase_comp hstar S hV s s.length le_rfl
  have hft1 : MaxContactReduction.strictTransformAtLength s' (H.comap q)
      = (MaxContactReduction.strictTransformAtLength s H).comap Dt.lastMap :=
    strictTransformAtLength_comap_lastMap S q s s' Dt hstar hV hV' H
  have hlist : List.map (fun Z : (s.obj s.length).IdealSheafData => Z.comap Dt.lastMap)
      [MaxContactReduction.strictTransformAtLength s H] = [MaxContactReduction.strictTransformAtLength s' (H.comap q)] :=
    congrArg (fun Z => [Z]) hft1.symm
  have hdrop : MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.map (fun Z : (s.obj s.length).IdealSheafData => Z.comap Dt.lastMap)
        (List.drop S.boundary.length (s.boundary s.length)))
      (List.drop (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length (s'.boundary s'.length)) :=
    NontrivialBoundary.sameNontrivialBoundary_symm
      (NontrivialBoundary.sameNontrivialBoundary_lastBoundary_drop S q s s' Dt hstar hV hV')
  have e1 : ((MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
        S.boundary.length).pullbackAlong (s'.obj s'.length)
      (Dt.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
        S.boundary.length).structMap) Dt.lastMap).boundary
      = List.map (fun D => D.comap Dt.lastMap)
        (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
          S.boundary.length).boundary :=
    MarkedIdealWithBoundary.pullbackAlong_boundary _ _ _ _
  have e2 := MaxContactCoverData.derivedTriple_boundary S s hftS
    [MaxContactReduction.strictTransformAtLength s H] S.boundary.length
  have e3 := MaxContactCoverData.derivedTriple_boundary (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
    [MaxContactReduction.strictTransformAtLength s' (H.comap q)] (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length
  have hbe : MarkedIdealWithBoundary.SameNontrivialBoundary
      ((MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
          S.boundary.length).pullbackAlong (s'.obj s'.length)
        (Dt.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
          S.boundary.length).structMap) Dt.lastMap).boundary
      (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).boundary := by
    rw [e1, e2, e3, hft1]
    exact NontrivialBoundary.sameNontrivialBoundary_cons hdrop
  have htake : List.take (0 + 1)
        (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
          [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).boundary
      = List.take (0 + 1)
        ((MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
            S.boundary.length).pullbackAlong (s'.obj s'.length)
          (Dt.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
            S.boundary.length).structMap) Dt.lastMap).boundary := by
    have t : [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        = [(MaxContactReduction.strictTransformAtLength s H).comap Dt.lastMap] := congrArg (fun Z => [Z]) hft1
    rw [e1, e2, e3]
    exact t
  have hjU : 0 < (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
      S.boundary.length).boundary.length := by
    rw [e2]
    simp
  have hjU' : 0 < (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
      [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).boundary.length := by
    rw [e3]
    simp
  have hOU := LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hftS
    [MaxContactReduction.strictTransformAtLength s H] S.boundary.length hVU
  have hDU := LowerDimReductionPullback.isBalanced_derivedTriple hstar S hV hm hO s hftS
    [MaxContactReduction.strictTransformAtLength s H] S.boundary.length hVU
  have hOU' := LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' hm hO' s'
    hftT [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
    (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length hVU'
  have hpb := NontrivialBoundary.pullbackAlong_derivedTriple_eq S q s s' Dt hstar hV hV' hftS hftT hsm
    [MaxContactReduction.strictTransformAtLength s H] S.boundary.length
    (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length
  have hEb : List.append
        (List.map (fun Z : (s.obj s.length).IdealSheafData => Z.comap Dt.lastMap)
          [MaxContactReduction.strictTransformAtLength s H])
        (List.drop (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length (s'.boundary s'.length))
      = (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
          [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).boundary :=
    (congrArg (fun L => List.append L
      (List.drop (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length (s'.boundary s'.length)))
      hlist).trans e3.symm
  have hEqLast :
      ((MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
          S.boundary.length).pullbackAlong (s'.obj s'.length)
        (Dt.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
          S.boundary.length).structMap) Dt.lastMap).withBoundary
        (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
          [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).boundary
      = MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
          [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length :=
    ((congrArg (fun L =>
        ((MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
            S.boundary.length).pullbackAlong (s'.obj s'.length)
          (Dt.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
            S.boundary.length).structMap) Dt.lastMap).withBoundary L) hEb).symm.trans hpb).trans
      (congrArg (fun E => MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT E
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) hlist)
  have hVtr : ∀ W : MarkedIdealWithBoundary.{u},
      W = MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length → W.IsAdmissible := by
    intro W hW
    subst hW
    exact hVU'
  have hPtr : ∀ W : MarkedIdealWithBoundary.{u},
      W = MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length → P W.krullDimSucc := by
    intro W hW
    subst hW
    exact hPU'
  have hOtr : ∀ W : MarkedIdealWithBoundary.{u},
      W = MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length → W.IsOrderBoundedByMult := by
    intro W hW
    subst hW
    exact hOU'
  have hjtr : ∀ W : MarkedIdealWithBoundary.{u},
      W = MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length → 0 < W.boundary.length := by
    intro W hW
    subst hW
    exact hjU'
  have hDtr : ∀ W : MarkedIdealWithBoundary.{u},
      W = MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length →
      ∀ hft : AlgebraicGeometry.LocallyOfFiniteType W.structMap, W.IsBalanced hft := by
    intro W hW hft
    subst hW
    exact LowerDimReductionPullback.isBalanced_derivedTriple hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' hm hO' s' hftT
      [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length hVU'
  have inner0 := @IsBoundaryDivisorReduction.smooth_pullback P 0 (A 0) Bl hspec
    (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H] S.boundary.length)
    hVU hPU hOU hDU hjU (s'.obj s'.length)
    (Dt.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
      S.boundary.length).structMap) Dt.lastMap (SequenceOfBlowupsPullback.smooth_lastMap Dt) rfl
    (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
      [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).boundary
    hbe htake (hVtr _ hEqLast) (hPtr _ hEqLast) (hOtr _ hEqLast) (hDtr _ hEqLast _)
    (hjtr _ hEqLast)
  have hp : Dt.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS
        [MaxContactReduction.strictTransformAtLength s H] S.boundary.length).structMap
      = (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
          [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).structMap :=
    (congrArg (fun mm => Dt.lastMap ≫ mm)
        (MaxContactCoverData.derivedTriple_structureMorphism S s hftS
          [MaxContactReduction.strictTransformAtLength s H] S.boundary.length)).trans
      ((NontrivialBoundary.lastMap_comp_structureMorphism S q s s' Dt).trans
        (MaxContactCoverData.derivedTriple_structureMorphism (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
          [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).symm)
  have hI : (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
        S.boundary.length).ideal.comap Dt.lastMap
      = (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
          [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).ideal :=
    (congrArg (fun J => J.comap Dt.lastMap)
        (LowerDimReductionPullback.ideal_derivedTriple S s hftS
          [MaxContactReduction.strictTransformAtLength s H] S.boundary.length)).trans
      ((NontrivialBoundary.tunedIdealAtLength_comap_lastMap S q s s' Dt hstar hV hV' hftS hftT hsm).trans
        (LowerDimReductionPullback.ideal_derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
          [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).symm)
  have hm2 : (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
        S.boundary.length).mult
      = (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
          [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).mult :=
    (MaxContactCoverData.derivedTriple_mult S s hftS
        [MaxContactReduction.strictTransformAtLength s H] S.boundary.length).trans
      (MaxContactCoverData.derivedTriple_mult (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).symm
  have inner : IsPullbackBlowupSequence Dt.lastMap
      (A 0 (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
          [MaxContactReduction.strictTransformAtLength s' (H.comap q)]
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length)).toSequenceOfBlowups
      (A 0 (MaxContactCoverData.derivedTriple S s hftS [MaxContactReduction.strictTransformAtLength s H]
          S.boundary.length)).toSequenceOfBlowups :=
    isPullbackBlowupSequence_congr (A 0) _ _ _ _ Dt.lastMap _ _ _ _ _ _ _ _ hp hI hm2 rfl inner0
  have hjlist : 0 < ([MaxContactReduction.strictTransformAtLength s H] ++
      (s.boundary s.length).drop S.boundary.length).length := by simp
  have hjlist' : 0 < ([MaxContactReduction.strictTransformAtLength s' (H.comap q)] ++
      (s'.boundary s'.length).drop (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).length := by simp
  obtain ⟨hmk, heq, -⟩ := LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A Bl 0 hspec
    (fun S₀ _ i => A i S₀) (fun _ _ _ => rfl) S hV hm hO s
    [MaxContactReduction.strictTransformAtLength s H] S.boundary.length hftS hdimU hPU hVU hjlist
    (BoundarySeparationBaseChange.orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated S s S.boundary.length hsep)
  obtain ⟨hmk', heq', -⟩ := LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A Bl 0 hspec
    (fun S₀ _ i => A i S₀) (fun _ _ _ => rfl) (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' hm hO' s'
    [MaxContactReduction.strictTransformAtLength s' (H.comap q)] (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length
    hftT hdimU' hPU' hVU' hjlist'
    (BoundarySeparationBaseChange.orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s'
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length hsep')
  rw [heq, heq']
  exact isPullbackBlowupSequence_append_of_two_fields q s _ s' _ hinv Dt
    (inner.nonempty_sequenceOfBlowupsPullback.some.toBlowupDataOfSeq)

end StrictTransformComparison

end FunctorialResolution.EmbeddedResolution

end
