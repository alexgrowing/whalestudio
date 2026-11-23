import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.RemoveIsoBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorFamilyCenters
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothBaseChangeOnDivisor
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

noncomputable abbrev fieldBaseChangeProjection (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K]
    (f : T.base →+* K) :=
  CategoryTheory.Limits.pullback.fst T.structMap (FunctorialResolution.EmbeddedResolution.specMapOfFieldHom T.base K f)

theorem get_eq_comap_fieldBaseChangeProjection (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (K : Type u) [Field K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData) (hjE : j < E'.length)
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary) :
    E'.get ⟨j, hjE⟩ = (T.boundary.get ⟨j, hj⟩).comap (fieldBaseChangeProjection T K f) := by
  have hj' : j < (T.baseChange K f).boundary.length := by
    have h := congrArg List.length htake
    simp only [List.length_take] at h
    omega
  have h1 : E'.get ⟨j, hjE⟩ = (T.baseChange K f).boundary.get ⟨j, hj'⟩ :=
    get_eq_get_of_take_succ_eq E' (T.baseChange K f).boundary j htake hjE hj'
  have key : ∀ (hh :
      j < (List.map (fun D => D.comap (fieldBaseChangeProjection T K f)) T.boundary).length),
      (List.map (fun D => D.comap (fieldBaseChangeProjection T K f)) T.boundary)[j]'hh
        = (T.boundary[j]'hj).comap (fieldBaseChangeProjection T K f) := by
    intro hh
    simp
  exact h1.trans (key hj')

structure FieldBaseChangeCompatibility : Prop where
  coSupport_baseChange :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (K : Type u) [Field K] (f : T.base →+* K)
      (E' : List (T.baseChange K f).scheme.IdealSheafData) (m : ℕ),
      orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal m =
        (fieldBaseChangeProjection T K f) ⁻¹' orderAtLeastLocus T.ideal m
  flat_proj :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] (f : T.base →+* K),
      AlgebraicGeometry.Flat (fieldBaseChangeProjection T K f)
  surjective_proj :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] (f : T.base →+* K),
      AlgebraicGeometry.Surjective (fieldBaseChangeProjection T K f)
  withBoundary_preIdeal :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
      (E' : List (T.baseChange K f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E' →
      ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
        List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary →
        ((T.baseChange K f).withBoundary E').IsAdmissible →
        DivisorReduction.containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
          (DivisorReduction.containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f)

structure RestrictedPrincipalizationFieldBaseChange (n : ℕ) (L : PrincipalizationAssignment.{u}) (j : ℕ) : Prop where
  isStrictPullbackSeq_lowerTop :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hO : T.IsOrderBoundedByMult)
      (_hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
      (_hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty) (K : Type u) [Field K] [CharZero K]
      (f : T.base →+* K) (E' : List (T.baseChange K f).scheme.IdealSheafData)
      (_hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E')
      (htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary)
      (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
      (_hdim' : ((T.baseChange K f).withBoundary E').krullDimSucc ≤ n)
      (_hO' : ((T.baseChange K f).withBoundary E').IsOrderBoundedByMult)
      (_hDB' : ((T.baseChange K f).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
      (hjE : j < E'.length)
      (_hcs' : (orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal T.mult).Nonempty)
      (_hZ : DivisorReduction.containedComponentsIdeal T j hj = ⊤)
      (_hZ' : DivisorReduction.containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE = ⊤),
      IsStrictPullbackBlowupSeq
        (DivisorReduction.divisorPullbackMap T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
          (DivisorReduction.lowerBoundaryWithoutBlowup T) (T.baseChange K f).scheme (fieldBaseChangeProjection T K f)
          (E'.get ⟨j, hjE⟩) (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake))
        (L (DivisorReduction.restrictToDivisor ((T.baseChange K f).withBoundary E') j hjE)).toSequenceOfBlowups
        (L (DivisorReduction.restrictToDivisor T j hj)).toSequenceOfBlowups
  isStrictPullbackSeq_lowerPre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hO : T.IsOrderBoundedByMult)
      (_hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
      (_hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty) (K : Type u) [Field K] [CharZero K]
      (f : T.base →+* K) (E' : List (T.baseChange K f).scheme.IdealSheafData)
      (_hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E')
      (htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary)
      (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
      (_hdim' : ((T.baseChange K f).withBoundary E').krullDimSucc ≤ n)
      (_hO' : ((T.baseChange K f).withBoundary E').IsOrderBoundedByMult)
      (_hDB' : ((T.baseChange K f).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
      (hjE : j < E'.length)
      (_hcs' : (orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal T.mult).Nonempty)
      (_hZ : DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤)
      (_hZ' : DivisorReduction.containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
        (DivisorReduction.containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f)),
      IsStrictPullbackBlowupSeq
        (DivisorReduction.divisorPullbackMap T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
          (DivisorReduction.lowerBoundaryAfterBlowup T j hj) (T.baseChange K f).scheme
          (fieldBaseChangeProjection T K f) (E'.get ⟨j, hjE⟩)
          (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake))
        (L (DivisorReduction.restrictTwistedToDivisor ((T.baseChange K f).withBoundary E') j hjE)).toSequenceOfBlowups
        (L (DivisorReduction.restrictTwistedToDivisor T j hj)).toSequenceOfBlowups

theorem divisorFamily_isStrictPullbackBlowupSeq_fieldBaseChange (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (hfbc : FieldBaseChangeCompatibility.{u}) (n : ℕ)
    (L : PrincipalizationAssignment.{u}) (j : ℕ) (hlow : RestrictedPrincipalizationFieldBaseChange n L j)
    (_hshape : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      orderAtLeastLocus T.ideal T.mult ≠ ∅ → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
    (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary)
    (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
    (hdim' : ((T.baseChange K f).withBoundary E').krullDimSucc ≤ n)
    (hO' : ((T.baseChange K f).withBoundary E').IsOrderBoundedByMult)
    (hDB' : ((T.baseChange K f).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
    (hjE : j < E'.length) :
    IsStrictPullbackBlowupSeq (fieldBaseChangeProjection T K f)
      (((canonicalAlgorithmRules hres).divisorFamily L j ((T.baseChange K f).withBoundary E')).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups) := by
  have : AlgebraicGeometry.IsNoetherian T.scheme :=
    DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
  have hNTb : AlgebraicGeometry.IsNoetherian ((T.baseChange K f).withBoundary E').scheme :=
    DivisorReduction.isNoetherian_scheme_of_isAdmissible _ hV'
  have : AlgebraicGeometry.IsNoetherian (T.baseChange K f).scheme := hNTb
  have : AlgebraicGeometry.IsNoetherian
      (CategoryTheory.Limits.pullback T.structMap (specMapOfFieldHom T.base K f)) := hNTb
  have : AlgebraicGeometry.Flat (fieldBaseChangeProjection T K f) := hfbc.flat_proj T K f
  have : AlgebraicGeometry.Flat
      (show (T.baseChange K f).scheme ⟶ T.scheme from fieldBaseChangeProjection T K f) :=
    hfbc.flat_proj T K f
  have : AlgebraicGeometry.Flat
      (show ((T.baseChange K f).withBoundary E').scheme ⟶ T.scheme from
        fieldBaseChangeProjection T K f) := hfbc.flat_proj T K f
  have hsurj0 : AlgebraicGeometry.Surjective (fieldBaseChangeProjection T K f) :=
    hfbc.surjective_proj T K f
  have : AlgebraicGeometry.Surjective
      (show (T.baseChange K f).scheme ⟶ T.scheme from fieldBaseChangeProjection T K f) :=
    hfbc.surjective_proj T K f
  have : AlgebraicGeometry.Surjective
      (show ((T.baseChange K f).withBoundary E').scheme ⟶ T.scheme from
        fieldBaseChangeProjection T K f) := hfbc.surjective_proj T K f
  have hmult : ((T.baseChange K f).withBoundary E').mult = T.mult := by
    rw [MarkedIdealWithBoundary.withBoundary_mult, MarkedIdealWithBoundary.baseChange_mult]
  have hcsEq : orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal T.mult =
      (fieldBaseChangeProjection T K f) ⁻¹' orderAtLeastLocus T.ideal T.mult :=
    hfbc.coSupport_baseChange T hV K f E' T.mult
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = ∅
  · have hcs'' : orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal
        ((T.baseChange K f).withBoundary E').mult = ∅ := by
      rw [hmult, hcsEq, hcs]
      exact Set.preimage_empty
    exact IsStrictPullbackBlowupSeq.of_length_zero _ _ _
      (divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j _ hV' hdim' hO' hDB' hjE hcs'')
      (divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j T hV hdim hO hbal hj hcs)
  · have hcsne : (orderAtLeastLocus T.ideal T.mult).Nonempty := Set.nonempty_iff_ne_empty.2 hcs
    have hcsne' : (orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal T.mult).Nonempty := by
      rw [hcsEq]
      exact hcsne.preimage hsurj0.surj
    have hcs' : orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal
        ((T.baseChange K f).withBoundary E').mult ≠ ∅ := by
      rw [hmult]
      exact Set.nonempty_iff_ne_empty.1 hcsne'
    have hpre : DivisorReduction.containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
        (DivisorReduction.containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f) :=
      hfbc.withBoundary_preIdeal T hV K f E' hBE j hj hjE htake hV'
    rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j ((T.baseChange K f).withBoundary E'),
      divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j T]
    rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j T hV hj hO hbal hcs with
      ⟨hZ, hpr, hmk0, heq⟩ | ⟨hZ, hb, hpr, hmk0, heq⟩
    · have hZ' : DivisorReduction.containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE = ⊤ := by
        rw [hpre, hZ]
        simp
        rfl
      rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j ((T.baseChange K f).withBoundary E')
          hV' hjE hO' hDB' hcs' with ⟨-, hpr2, hmk2, heq2⟩ | ⟨hZ2, -⟩
      · have hlower := hlow.isStrictPullbackSeq_lowerTop T hV hdim hO hbal hj hcsne K f E' hBE
          htake hV' hdim' hO' hDB' hjE hcsne' hZ hZ'
        have hlower2 := IsStrictPullbackBlowupSeq.ofMarkedSequence
          (DivisorReduction.divisorPullbackMap T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) (T.baseChange K f).scheme
            (fieldBaseChangeProjection T K f) (E'.get ⟨j, hjE⟩)
            (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake))
          (L (DivisorReduction.restrictToDivisor ((T.baseChange K f).withBoundary E') j hjE))
          (L (DivisorReduction.restrictToDivisor T j hj)) hlower
        rw [heq hmk0, heq2 hmk2, BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
          BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
        exact hfacts.isStrictPullbackSeq_ambientTower T.scheme (T.baseChange K f).scheme
          (T.boundary.get ⟨j, hj⟩).subscheme (E'.get ⟨j, hjE⟩).subscheme
          (T.boundary.get ⟨j, hj⟩).subschemeι (E'.get ⟨j, hjE⟩).subschemeι
          (fieldBaseChangeProjection T K f)
          (DivisorReduction.divisorPullbackMap T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) (T.baseChange K f).scheme
            (fieldBaseChangeProjection T K f) (E'.get ⟨j, hjE⟩)
            (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake))
          ((DivisorReduction.isPullback_divisorPullbackMap hbc T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) (T.baseChange K f).scheme
            (fieldBaseChangeProjection T K f) (E'.get ⟨j, hjE⟩)
            (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake)).flip)
          (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData
          (MarkedBlowupSequenceData.ofMarkedSequence
            (L (DivisorReduction.restrictToDivisor ((T.baseChange K f).withBoundary E') j hjE))).toBlowupSequenceData
          hpr hpr2 hlower2
      · exact absurd hZ' hZ2
    · have hZ' : DivisorReduction.containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE ≠ ⊤ := by
        rw [hpre]
        exact DivisorReduction.comap_ne_top_of_surjective hbc (fieldBaseChangeProjection T K f)
          (DivisorReduction.containedComponentsIdeal T j hj) hZ
      rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j ((T.baseChange K f).withBoundary E')
          hV' hjE hO' hDB' hcs' with ⟨hZ2, -⟩ | ⟨-, hb2, hpr2, hmk2, heq2⟩
      · exact absurd hZ2 hZ'
      · have hlower := hlow.isStrictPullbackSeq_lowerPre T hV hdim hO hbal hj hcsne K f E' hBE
          htake hV' hdim' hO' hDB' hjE hcsne' hZ hpre
        have hlower2 := IsStrictPullbackBlowupSeq.ofMarkedSequence
          (DivisorReduction.divisorPullbackMap T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
            (DivisorReduction.lowerBoundaryAfterBlowup T j hj) (T.baseChange K f).scheme
            (fieldBaseChangeProjection T K f) (E'.get ⟨j, hjE⟩)
            (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake))
          (L (DivisorReduction.restrictTwistedToDivisor ((T.baseChange K f).withBoundary E') j hjE))
          (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hlower
        have key : IsStrictPullbackBlowupSeq (fieldBaseChangeProjection T K f)
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian
              ((T.baseChange K f).withBoundary E') j hjE
              (DivisorReduction.lowerIdealAfterBlowup ((T.baseChange K f).withBoundary E') j hjE)
              (DivisorReduction.lowerBoundaryAfterBlowup ((T.baseChange K f).withBoundary E') j hjE)
              (L (DivisorReduction.restrictTwistedToDivisor ((T.baseChange K f).withBoundary E') j hjE))
              hpr2).toSequenceOfBlowups
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
              (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)
              (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr).toSequenceOfBlowups :=
          hfacts.isStrictPullbackSeq_ambientTower T.scheme (T.baseChange K f).scheme
            (T.boundary.get ⟨j, hj⟩).subscheme (E'.get ⟨j, hjE⟩).subscheme
            (T.boundary.get ⟨j, hj⟩).subschemeι (E'.get ⟨j, hjE⟩).subschemeι
            (fieldBaseChangeProjection T K f)
            (DivisorReduction.divisorPullbackMap T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) (T.baseChange K f).scheme
              (fieldBaseChangeProjection T K f) (E'.get ⟨j, hjE⟩)
              (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake))
            ((DivisorReduction.isPullback_divisorPullbackMap hbc T j hj
              (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)
              (T.baseChange K f).scheme (fieldBaseChangeProjection T K f) (E'.get ⟨j, hjE⟩)
              (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake)).flip)
            (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData
            (MarkedBlowupSequenceData.ofMarkedSequence
              (L (DivisorReduction.restrictTwistedToDivisor ((T.baseChange K f).withBoundary E') j
                hjE))).toBlowupSequenceData
            hpr hpr2 hlower2
        have hb2' : Blowup.IsBlowupAlongIdealSheaf (𝟙 ((T.baseChange K f).withBoundary E').scheme)
            (DivisorReduction.containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE) := hb2
        rw [hpre] at hb2'
        rw [heq hmk0, heq2 hmk2, BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
          BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
          BlowupSequenceData.prepend_toSequenceOfBlowups_congr hpre hb2 hb2'
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian
              ((T.baseChange K f).withBoundary E') j hjE
              (DivisorReduction.lowerIdealAfterBlowup ((T.baseChange K f).withBoundary E') j hjE)
              (DivisorReduction.lowerBoundaryAfterBlowup ((T.baseChange K f).withBoundary E') j hjE)
              (L (DivisorReduction.restrictTwistedToDivisor ((T.baseChange K f).withBoundary E') j hjE)) hpr2)]
        exact key.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb hb2'

theorem divisorFamily_isPullbackSequenceOfBlowups_fieldBaseChange (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (hfbc : FieldBaseChangeCompatibility.{u}) (n : ℕ)
    (L : PrincipalizationAssignment.{u}) (j : ℕ) (hlow : RestrictedPrincipalizationFieldBaseChange n L j)
    (hshape : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      orderAtLeastLocus T.ideal T.mult ≠ ∅ → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj)
    (hcenters : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.krullDimSucc ≤ n → T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
      ∀ i, i < ((canonicalAlgorithmRules hres).divisorFamily L j T).length →
        ((((canonicalAlgorithmRules hres).divisorFamily L j T).center i).support.carrier).Nonempty)
    (hprune : ∀ (Y : Scheme.{u}) (s : SequenceOfBlowups Y),
      (∀ i, i < s.length → s.center i ≠ ⊤) → s.withoutIsoBlowups.Isomorphic s)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
    (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary)
    (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
    (hdim' : ((T.baseChange K f).withBoundary E').krullDimSucc ≤ n)
    (hO' : ((T.baseChange K f).withBoundary E').IsOrderBoundedByMult)
    (hDB' : ((T.baseChange K f).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
    (hjE : j < E'.length) :
    IsPullbackBlowupSequence (fieldBaseChangeProjection T K f)
      (((canonicalAlgorithmRules hres).divisorFamily L j ((T.baseChange K f).withBoundary E')).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups) := by
  have hstrict := divisorFamily_isStrictPullbackBlowupSeq_fieldBaseChange hres hfacts hbc hfbc n L j hlow hshape
    T hV hdim hO hbal hj K f E' hBE htake hV' hdim' hO' hDB' hjE
  refine hstrict.isPullbackSequenceOfBlowups_withoutIsoBlowups.of_isomorphic ?_
  refine hprune _ _ ?_
  intro i hi
  exact (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mp
    (hcenters ((T.baseChange K f).withBoundary E') hV' hdim' hO' hDB' hjE i hi)

end FunctorialResolution.EmbeddedResolution
