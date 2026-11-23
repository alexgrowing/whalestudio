import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorFamilyCenters
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

private theorem isStrictPullbackBlowupSeq_ofSequenceOfBlowups {X X' : Scheme.{u}} (φ : X' ⟶ X) (B' : SequenceOfBlowups X')
    (B : SequenceOfBlowups X) (h : IsStrictPullbackBlowupSeq φ B' B) :
    IsStrictPullbackBlowupSeq φ (BlowupSequenceData.ofSequenceOfBlowups B').toSequenceOfBlowups (BlowupSequenceData.ofSequenceOfBlowups B).toSequenceOfBlowups := by
  obtain ⟨hlen, σ, h0, hpb, hc⟩ := h
  have hlA : (BlowupSequenceData.ofSequenceOfBlowups B').toSequenceOfBlowups.length = B'.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.ofSequenceOfBlowups_length]
  have hlB : (BlowupSequenceData.ofSequenceOfBlowups B).toSequenceOfBlowups.length = B.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.ofSequenceOfBlowups_length]
  refine ⟨by rw [hlA, hlB, hlen], fun i hi => σ i (hi.trans_eq hlA), ?_, ?_, ?_⟩
  · simp only [BlowupSequenceData.toSequenceOfBlowups_isoObjZero, BlowupSequenceData.ofSequenceOfBlowups_isoObjZero]
    exact h0
  · intro i hi
    simp only [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.ofSequenceOfBlowups_blowupMorphism]
    exact hpb i (hi.trans_eq hlA)
  · intro i hi
    simp only [BlowupSequenceData.toSequenceOfBlowups_center, BlowupSequenceData.ofSequenceOfBlowups_center]
    exact hc i (hi.trans_eq hlA)

theorem IsStrictPullbackBlowupSeq.ofMarkedSequence {A B : MarkedIdealWithBoundary.{u}} (φ : A.scheme ⟶ B.scheme)
    (sA : A.SequenceOfBlowups) (sB : B.SequenceOfBlowups)
    (h : IsStrictPullbackBlowupSeq φ sA.toSequenceOfBlowups sB.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq φ (MarkedBlowupSequenceData.ofMarkedSequence sA).toBlowupSequenceData.toSequenceOfBlowups
      (MarkedBlowupSequenceData.ofMarkedSequence sB).toBlowupSequenceData.toSequenceOfBlowups := by
  rw [MarkedBlowupSequenceData.blowupSequenceData_ofMarkedSequence sA,
    MarkedBlowupSequenceData.blowupSequenceData_ofMarkedSequence sB]
  exact isStrictPullbackBlowupSeq_ofSequenceOfBlowups φ _ _ h

theorem BlowupSequenceData.prepend_toSequenceOfBlowups_congr {X : Scheme.{u}} {Z Z' : X.IdealSheafData} (hZZ : Z = Z')
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z') (d : BlowupSequenceData X) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups = (BlowupSequenceData.prepend Z' hZ' d).toSequenceOfBlowups := by
  subst hZZ
  rfl

structure FlatOfSmooth : Prop where
  flat_of_smooth : ∀ (X Y : Scheme.{u}) (f : Y ⟶ X), AlgebraicGeometry.Smooth f →
    AlgebraicGeometry.Flat f

namespace DivisorReduction

structure StrictPullbackOfSmoothBaseChangeOnDivisor (n : ℕ) (L : PrincipalizationAssignment.{u}) (j : ℕ) : Prop where
  isStrictPullbackSeq_lowerTop :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hO : T.IsOrderBoundedByMult)
      (_hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
      (_hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty) (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.Surjective h]
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
      IsStrictPullbackBlowupSeq
        (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩)
          (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
        (L (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE)).toSequenceOfBlowups
        (L (restrictToDivisor T j hj)).toSequenceOfBlowups
  isStrictPullbackSeq_lowerPre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hO : T.IsOrderBoundedByMult)
      (_hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
      (_hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty) (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.Surjective h]
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
      (_hZ' : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE =
        (containedComponentsIdeal T j hj).comap h),
      IsStrictPullbackBlowupSeq
        (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h (E'.get ⟨j, hjE⟩)
          (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
        (L (restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE)).toSequenceOfBlowups
        (L (restrictTwistedToDivisor T j hj)).toSequenceOfBlowups

def DivisorReductionSeqEqAmbient (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (L : PrincipalizationAssignment.{u}) (j : ℕ)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length) : Prop :=
  letI : AlgebraicGeometry.IsNoetherian T.scheme := isNoetherian_scheme_of_isAdmissible T hV
  (containedComponentsIdeal T j hj = ⊤ ∧
      ∃ (hpr : (MarkedBlowupSequenceData.ofMarkedSequence (L (restrictToDivisor T j hj))).CentersContainNoComponent)
        (hmk : (ambientBlowupSeq hres blowupPreservesNoetherian T j hj (lowerIdealWithoutBlowup T)
            (lowerBoundaryWithoutBlowup T) (L (restrictToDivisor T j hj)) hpr).IsMarked
            T.structMap T.ideal T.mult T.boundary),
        divisorReductionSeq hres blowupPreservesNoetherian T (fun S _ => L S) j =
          ((ambientBlowupSeq hres blowupPreservesNoetherian T j hj (lowerIdealWithoutBlowup T)
              (lowerBoundaryWithoutBlowup T) (L (restrictToDivisor T j hj)) hpr).toMarkedBlowupSequenceData
              T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups) ∨
    (containedComponentsIdeal T j hj ≠ ⊤ ∧
      ∃ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence (L (restrictTwistedToDivisor T j hj))).CentersContainNoComponent)
        (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
            (ambientBlowupSeq hres blowupPreservesNoetherian T j hj (lowerIdealAfterBlowup T j hj)
              (lowerBoundaryAfterBlowup T j hj) (L (restrictTwistedToDivisor T j hj)) hpr)).IsMarked
            T.structMap T.ideal T.mult T.boundary),
        divisorReductionSeq hres blowupPreservesNoetherian T (fun S _ => L S) j =
          ((BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
              (ambientBlowupSeq hres blowupPreservesNoetherian T j hj (lowerIdealAfterBlowup T j hj)
                (lowerBoundaryAfterBlowup T j hj) (L (restrictTwistedToDivisor T j hj)) hpr)).toMarkedBlowupSequenceData
              T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups)

theorem divisorFamily_isStrictPullbackBlowupSeq_of_smooth (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : SmoothPullbackCompatibility.{u}) (hsf : FlatOfSmooth.{u}) (n : ℕ) (L : PrincipalizationAssignment.{u})
    (j : ℕ) (hlow : StrictPullbackOfSmoothBaseChangeOnDivisor n L j)
    (hshape : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReductionSeqEqAmbient hres L j T hV hj)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.Surjective h]
    (hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary)
    (hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible)
    (hdim' : ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc ≤ n)
    (hO' : ((T.pullbackAlong Y q h).withBoundary E').IsOrderBoundedByMult)
    (hDB' : ((T.pullbackAlong Y q h).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
    (hjE : j < E'.length) :
    IsStrictPullbackBlowupSeq h
      (((canonicalAlgorithmRules hres).divisorFamily L j
        ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups) := by
  classical
  have : AlgebraicGeometry.IsNoetherian T.scheme := isNoetherian_scheme_of_isAdmissible T hV
  have : AlgebraicGeometry.IsNoetherian
      ((T.pullbackAlong Y q h).withBoundary E').scheme :=
    isNoetherian_scheme_of_isAdmissible _ hV'
  have : AlgebraicGeometry.IsNoetherian Y := isNoetherian_scheme_of_isAdmissible _ hV'
  have : AlgebraicGeometry.Flat h := hsf.flat_of_smooth T.scheme Y h inferInstance
  rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j ((T.pullbackAlong Y q h).withBoundary E'),
    divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j T]
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = ∅
  · have hcs2 : orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hx
      rw [orderAtLeastLocus_withBoundary_pullbackAlong hbc T hV Y q h hq E' T.mult, hcs] at hx
      exact hx
    rw [divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian
        ((T.pullbackAlong Y q h).withBoundary E') (fun S _ => L S) j hjE hcs2,
      divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian T
        (fun S _ => L S) j hj hcs]
    exact IsStrictPullbackBlowupSeq.of_length_zero h _ _ rfl rfl
  · have hcsne : (orderAtLeastLocus T.ideal T.mult).Nonempty := Set.nonempty_iff_ne_empty.mpr hcs
    have hcsne' : (orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult).Nonempty := by
      obtain ⟨x, hx⟩ := hcsne
      obtain ⟨y, rfl⟩ := h.surjective x
      refine ⟨y, ?_⟩
      rw [orderAtLeastLocus_withBoundary_pullbackAlong hbc T hV Y q h hq E' T.mult]
      exact hx
    have hpre : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE
        = (containedComponentsIdeal T j hj).comap h :=
      hbc.preIdeal_comap T hV Y q h hq E' hBE j hj hjE htake hV'
    have hsT := hshape T hV hj hdim hO hbal hcsne
    have hsT' := hshape ((T.pullbackAlong Y q h).withBoundary E') hV' hjE hdim' hO' hDB' hcsne'
    unfold DivisorReductionSeqEqAmbient at hsT hsT'
    rcases hsT with ⟨hZ, hpr, _hmk, hstep⟩ | ⟨hZ, hb, hpr, _hmk, hstep⟩
    · rcases hsT' with ⟨hZ', hpr', _hmk', hstep'⟩ | ⟨hZ', _hb', _hpr', _hmk', _hstep'⟩
      · rw [hstep, hstep', BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
          BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
        exact hfacts.isStrictPullbackSeq_ambientTower _ _ _ _
          (T.boundary.get ⟨j, hj⟩).subschemeι (E'.get ⟨j, hjE⟩).subschemeι h
          (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.get ⟨j, hjE⟩)
            (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
          ((isPullback_divisorPullbackMap hbc T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h
            (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake)).flip)
          (MarkedBlowupSequenceData.ofMarkedSequence (L (restrictToDivisor T j hj))).toBlowupSequenceData
          (MarkedBlowupSequenceData.ofMarkedSequence
            (L (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE))).toBlowupSequenceData
          hpr hpr'
          (IsStrictPullbackBlowupSeq.ofMarkedSequence _ _ _
            (hlow.isStrictPullbackSeq_lowerTop T hV hdim hO hbal hj hcsne Y q h hq E' hBE htake
              hV' hdim' hO' hDB' hjE hcsne' hZ hZ'))
      · exfalso
        have htc : (containedComponentsIdeal T j hj).comap h = ⊤ := by
          rw [hZ]
          simp
        exact hZ' (hpre.trans htc)
    · rcases hsT' with ⟨hZ', _hpr', _hmk', _hstep'⟩ | ⟨_hZ', hb', hpr', _hmk', hstep'⟩
      · have hcontra : (containedComponentsIdeal T j hj).comap h = ⊤ := by rw [← hpre]; exact hZ'
        exact absurd hcontra (comap_ne_top_of_surjective hbc h (containedComponentsIdeal T j hj) hZ)
      · rw [hstep, hstep', BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
          BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
        have hb'' : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) ((containedComponentsIdeal T j hj).comap h) :=
          isBlowupAlongIdealSheaf_id_comap_containedComponentsIdeal hres hfacts j T Y q h E' hV' hj hjE hpre
        have hamb := hfacts.isStrictPullbackSeq_ambientTower _ _ _ _
          (T.boundary.get ⟨j, hj⟩).subschemeι (E'.get ⟨j, hjE⟩).subschemeι h
          (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
            (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
          ((isPullback_divisorPullbackMap hbc T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
            (E'.get ⟨j, hjE⟩) (get_eq_comap_get_boundary T j hj Y q h E' hjE htake)).flip)
          (MarkedBlowupSequenceData.ofMarkedSequence (L (restrictTwistedToDivisor T j hj))).toBlowupSequenceData
          (MarkedBlowupSequenceData.ofMarkedSequence
            (L (restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE))).toBlowupSequenceData
          hpr hpr'
          (IsStrictPullbackBlowupSeq.ofMarkedSequence _ _ _
            (hlow.isStrictPullbackSeq_lowerPre T hV hdim hO hbal hj hcsne Y q h hq E' hBE htake
              hV' hdim' hO' hDB' hjE hcsne' hZ hpre))
        have key := hamb.prepend (containedComponentsIdeal T j hj) hb hb''
        rw [BlowupSequenceData.prepend_toSequenceOfBlowups_congr hpre hb' hb''
          (ambientBlowupSeq hres blowupPreservesNoetherian
            ((T.pullbackAlong Y q h).withBoundary E') j hjE
            (lowerIdealAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE)
            (lowerBoundaryAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE)
            (L (restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE)) hpr')]
        exact key

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
