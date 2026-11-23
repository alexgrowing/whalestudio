import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorFamilyCenters
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothBaseChangeOnDivisor
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Prepend
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

structure EmptyPulledBackCenterCompatibility : Prop where
  lowerIdealPre_comap_eq_lowerIdealTop_comap :
    ∀ (T : MarkedIdealWithBoundary.{u}) (_hV : T.IsAdmissible) (_hO : T.IsOrderBoundedByMult) (j : ℕ)
      (hj : j < T.boundary.length) (Y : Scheme.{u}) (h : Y ⟶ T.scheme),
      (containedComponentsIdeal T j hj).comap h = ⊤ →
      (lowerIdealAfterBlowup T j hj).comap h = (lowerIdealWithoutBlowup T).comap h
  boundaryEquiv_restrictedBoundary_comap_of_center_comap_eq_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) (_hV : T.IsAdmissible) (j : ℕ) (hj : j < T.boundary.length)
      (Y : Scheme.{u}) (h : Y ⟶ T.scheme),
      (containedComponentsIdeal T j hj).comap h = ⊤ →
      MarkedIdealWithBoundary.SameNontrivialBoundary
        (List.map (fun D => D.comap h)
          (List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j)))
        (List.map (fun D => D.comap h)
          (List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j)))

structure IsPullbackSeqOfEmptyBlowupSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (L : PrincipalizationAssignment.{u}) (j : ℕ) : Prop where
  isPullbackSeq_of_coSupport_empty :
    ∀ (T : MarkedIdealWithBoundary.{u}) (_hV : T.IsAdmissible) (_hj : j < T.boundary.length) (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) [AlgebraicGeometry.Smooth h],
      h ≫ T.structMap = q →
      ∀ (E' : List Y.IdealSheafData),
        ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
        (orderAtLeastLocus T.ideal T.mult).Nonempty →
        orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult = ∅ →
        ∀ (B' : SequenceOfBlowups Y), B'.length = 0 →
          IsPullbackBlowupSequence h B' (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups)
  isPullbackSeq_of_length_eq_zero :
    ∀ (X X' : Scheme.{u}) (φ : X' ⟶ X) (B' : SequenceOfBlowups X') (B : SequenceOfBlowups X),
      B'.length = 0 → B.length = 0 → IsPullbackBlowupSequence φ B' B
  isPullbackSeq_ofMarkedSeq :
    ∀ (A B : MarkedIdealWithBoundary.{u}) (φ : A.scheme ⟶ B.scheme) (sA : A.SequenceOfBlowups) (sB : B.SequenceOfBlowups),
      IsPullbackBlowupSequence φ sA.toSequenceOfBlowups sB.toSequenceOfBlowups →
      IsPullbackBlowupSequence φ (MarkedBlowupSequenceData.ofMarkedSequence sA).toBlowupSequenceData.toSequenceOfBlowups
        (MarkedBlowupSequenceData.ofMarkedSequence sB).toBlowupSequenceData.toSequenceOfBlowups

structure RestrictedPrincipalizationSmoothPullback (n : ℕ) (L : PrincipalizationAssignment.{u}) (j : ℕ) : Prop where
  isPullbackSeq_lowerMixed :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hO : T.IsOrderBoundedByMult)
      (_hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
      (_hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty) (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h]
      (_hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
      (_hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
      (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary)
      (hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible)
      (_hdim' : ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc ≤ n)
      (_hO' : ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult)
      (_hDB' : ((T.pullbackAlong Y q h).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
      (hjE : j < E'.length)
      (_hcs' : (orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult).Nonempty)
      (_hZ : containedComponentsIdeal T j hj ≠ ⊤)
      (_hZc : (containedComponentsIdeal T j hj).comap h = ⊤)
      (_hZ' : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = ⊤),
      IsPullbackBlowupSequence
        (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
          (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
        (L (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE)).toSequenceOfBlowups
        (L (restrictTwistedToDivisor T j hj)).toSequenceOfBlowups
  isPullbackSeq_lowerTop :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hO : T.IsOrderBoundedByMult)
      (_hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
      (_hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty) (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h]
      (_hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
      (_hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
      (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary)
      (hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible)
      (_hdim' : ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc ≤ n)
      (_hO' : ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult)
      (_hDB' : ((T.pullbackAlong Y q h).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
      (hjE : j < E'.length)
      (_hcs' : (orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult).Nonempty)
      (_hZ : containedComponentsIdeal T j hj = ⊤)
      (_hZ' : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = ⊤),
      IsPullbackBlowupSequence
        (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩)
          (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
        (L (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE)).toSequenceOfBlowups
        (L (restrictToDivisor T j hj)).toSequenceOfBlowups
  isPullbackSeq_lowerPre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hO : T.IsOrderBoundedByMult)
      (_hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
      (_hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty) (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h]
      (_hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
      (_hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
      (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary)
      (hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible)
      (_hdim' : ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc ≤ n)
      (_hO' : ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult)
      (_hDB' : ((T.pullbackAlong Y q h).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
      (hjE : j < E'.length)
      (_hcs' : (orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult).Nonempty)
      (_hZ : containedComponentsIdeal T j hj ≠ ⊤)
      (_hZc : (containedComponentsIdeal T j hj).comap h ≠ ⊤)
      (_hZ' : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE =
        (containedComponentsIdeal T j hj).comap h),
      IsPullbackBlowupSequence
        (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
          (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
        (L (restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE)).toSequenceOfBlowups
        (L (restrictTwistedToDivisor T j hj)).toSequenceOfBlowups

theorem divisorFamily_isPullbackBlowupSequence (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : SmoothPullbackCompatibility.{u}) (hsf : FlatOfSmooth.{u}) (n : ℕ) (L : PrincipalizationAssignment.{u})
    (j : ℕ) (hdel : IsPullbackSeqOfEmptyBlowupSeq hres L j)
    (hlow : RestrictedPrincipalizationSmoothPullback n L j)
    (hshape : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReductionSeqEqAmbient hres L j T hV hj)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h]
    (hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary)
    (hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible)
    (hdim' : ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc ≤ n)
    (hO' : ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult)
    (hDB' : ((T.pullbackAlong Y q h).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
    (hjE : j < E'.length) :
    IsPullbackBlowupSequence h
      (((canonicalAlgorithmRules hres).divisorFamily L j
        ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups) := by
  classical
  have hmult : ((T.pullbackAlong Y q h).withBoundary E').mult = T.mult := rfl
  by_cases hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty
  · by_cases hcs' : (orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult).Nonempty
    · have hZeq : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE
          = (containedComponentsIdeal T j hj).comap h :=
        hbc.preIdeal_comap T hV Y q h hq E' hBE j hj hjE htake hV'
      have _hNT : AlgebraicGeometry.IsNoetherian T.scheme := isNoetherian_scheme_of_isAdmissible T hV
      have _hNY : AlgebraicGeometry.IsNoetherian Y :=
        isNoetherian_scheme_of_isAdmissible ((T.pullbackAlong Y q h).withBoundary E') hV'
      have _hfl : AlgebraicGeometry.Flat h := hsf.flat_of_smooth T.scheme Y h inferInstance
      rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j T,
        divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j ((T.pullbackAlong Y q h).withBoundary E')]
      rcases hshape T hV hj hdim hO hbal hcs with ⟨hZ, hpr, hmk, heq⟩ | ⟨hZ, hb, hpr, hmk, heq⟩
      · rcases hshape ((T.pullbackAlong Y q h).withBoundary E') hV' hjE hdim' hO' hDB' hcs' with
          ⟨hZ', hpr', hmk', heq'⟩ | ⟨hZ', hb', hpr', hmk', heq'⟩
        · rw [heq, heq', BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
            BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
          exact hfacts.isPullbackSeq_ambientTower T.scheme Y
            (T.boundary.get ⟨j, hj⟩).subscheme (E'.get ⟨j, hjE⟩).subscheme
            (T.boundary.get ⟨j, hj⟩).subschemeι (E'.get ⟨j, hjE⟩).subschemeι h
            (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩)
              (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
            ((isPullback_divisorPullbackMap hbc T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h
              (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake)).flip)
            (MarkedBlowupSequenceData.ofMarkedSequence (L (restrictToDivisor T j hj))).toBlowupSequenceData
            (MarkedBlowupSequenceData.ofMarkedSequence
              (L (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE))).toBlowupSequenceData
            hpr hpr'
            (hdel.isPullbackSeq_ofMarkedSeq
              (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE) (restrictToDivisor T j hj)
              (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩)
                (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
              (L (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE))
              (L (restrictToDivisor T j hj))
              (hlow.isPullbackSeq_lowerTop T hV hdim hO hbal hj hcs Y q h hq E' hBE htake hV'
                hdim' hO' hDB' hjE hcs' hZ hZ'))
        · refine absurd ?_ hZ'
          rw [hZeq, hZ]
          exact AlgebraicGeometry.Scheme.IdealSheafData.comap_top ..
      · rcases hshape ((T.pullbackAlong Y q h).withBoundary E') hV' hjE hdim' hO' hDB' hcs' with
          ⟨hZ', hpr', hmk', heq'⟩ | ⟨hZ', hb', hpr', hmk', heq'⟩
        · have htop : (containedComponentsIdeal T j hj).comap h = ⊤ := hZeq.symm.trans hZ'
          rw [heq, heq', BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
            BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
          refine IsPullbackBlowupSequence.prepend_of_comap_eq_top ?_ (containedComponentsIdeal T j hj) hb htop
          exact hfacts.isPullbackSeq_ambientTower T.scheme Y
            (T.boundary.get ⟨j, hj⟩).subscheme (E'.get ⟨j, hjE⟩).subscheme
            (T.boundary.get ⟨j, hj⟩).subschemeι (E'.get ⟨j, hjE⟩).subschemeι h
            (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
              (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
            ((isPullback_divisorPullbackMap hbc T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)
              Y h (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake)).flip)
            (MarkedBlowupSequenceData.ofMarkedSequence (L (restrictTwistedToDivisor T j hj))).toBlowupSequenceData
            (MarkedBlowupSequenceData.ofMarkedSequence
              (L (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE))).toBlowupSequenceData
            hpr hpr'
            (hdel.isPullbackSeq_ofMarkedSeq
              (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE) (restrictTwistedToDivisor T j hj)
              (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
                (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
              (L (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE))
              (L (restrictTwistedToDivisor T j hj))
              (hlow.isPullbackSeq_lowerMixed T hV hdim hO hbal hj hcs Y q h hq E' hBE htake hV'
                hdim' hO' hDB' hjE hcs' hZ htop hZ'))
        · have hne : (containedComponentsIdeal T j hj).comap h ≠ ⊤ := fun hcc => hZ' (hZeq.trans hcc)
          have hbb : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) ((containedComponentsIdeal T j hj).comap h) :=
            isBlowupAlongIdealSheaf_id_comap_containedComponentsIdeal hres hfacts j T Y q h E' hV' hj hjE hZeq
          rw [heq, heq', BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
            BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
            BlowupSequenceData.prepend_toSequenceOfBlowups_congr hZeq hb' hbb]
          refine IsPullbackBlowupSequence.prepend_of_comap_ne_top ?_ (containedComponentsIdeal T j hj) hb hbb hne
          exact hfacts.isPullbackSeq_ambientTower T.scheme Y
            (T.boundary.get ⟨j, hj⟩).subscheme (E'.get ⟨j, hjE⟩).subscheme
            (T.boundary.get ⟨j, hj⟩).subschemeι (E'.get ⟨j, hjE⟩).subschemeι h
            (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
              (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
            ((isPullback_divisorPullbackMap hbc T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)
              Y h (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake)).flip)
            (MarkedBlowupSequenceData.ofMarkedSequence (L (restrictTwistedToDivisor T j hj))).toBlowupSequenceData
            (MarkedBlowupSequenceData.ofMarkedSequence
              (L (restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE))).toBlowupSequenceData
            hpr hpr'
            (hdel.isPullbackSeq_ofMarkedSeq
              (restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE) (restrictTwistedToDivisor T j hj)
              (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
                (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
              (L (restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE))
              (L (restrictTwistedToDivisor T j hj))
              (hlow.isPullbackSeq_lowerPre T hV hdim hO hbal hj hcs Y q h hq E' hBE htake hV'
                hdim' hO' hDB' hjE hcs' hZ hne hZeq))
    · have hempty : orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hcs'
      have hlen' : (((canonicalAlgorithmRules hres).divisorFamily L j
          ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups).length = 0 := by
        refine divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j _ hV' hdim' hO' hDB' hjE ?_
        rw [hmult]
        exact hempty
      exact hdel.isPullbackSeq_of_coSupport_empty T hV hj Y q h hq E' hV' hcs hempty _ hlen'
  · have hempty : orderAtLeastLocus T.ideal T.mult = ∅ := Set.not_nonempty_iff_eq_empty.mp hcs
    have hempty' : orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult = ∅ := by
      rw [orderAtLeastLocus_withBoundary_pullbackAlong hbc T hV Y q h hq E' T.mult, hempty]
      exact Set.preimage_empty
    have hlen : (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups).length = 0 :=
      divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j T hV hdim hO hbal hj hempty
    have hlen' : (((canonicalAlgorithmRules hres).divisorFamily L j
        ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups).length = 0 := by
      refine divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j _ hV' hdim' hO' hDB' hjE ?_
      rw [hmult]
      exact hempty'
    exact hdel.isPullbackSeq_of_length_eq_zero T.scheme Y h _ _ hlen' hlen

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
