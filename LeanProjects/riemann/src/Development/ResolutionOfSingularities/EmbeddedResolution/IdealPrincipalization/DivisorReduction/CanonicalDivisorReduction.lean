import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelSupport
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.EmptyOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.FieldBaseChangeCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.OrderLocusFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorRestrictionFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.RestrictedBaseChangeComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BalancedDivisorReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.InducedSubschemePullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.EmptyPulledBackCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientEmbeddingCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PrependedAmbientSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PushedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BoundaryComponentsInOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.NontrivialBoundaryReindexing
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionStepProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerIdealFunctoriality
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BaseChangeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.KernelOfAmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderAlongBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.OrderOffExceptionalDivisor
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.DimensionNonincreasing
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      ∃ B : T.scheme.IdealSheafData, B * DivisorReduction.containedComponentsIdeal T j hj ^ T.mult = T.ideal := by
  intro T hV _ j hj
  obtain ⟨J, hJ⟩ := exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj
  exact ⟨J, by rw [mul_comm]; exact hJ⟩

private theorem orderAtComapOffExceptionalLocus : OrderAtComapOffExceptionalLocus.{u} := by
  delta OrderAtComapOffExceptionalLocus
  exact fun T hT X' π Z hπ x' hx' A =>
    orderAt_comap_eq_of_notMem_exceptionalIdeal T hT Z X' π hπ x' hx' A

private theorem smoothPullbackCompatibility_of_divisorReductionTermination (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) :
    DivisorReduction.SmoothPullbackCompatibility.{u} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact comap_ne_top_of_surjective
  · intro T hV Y q h inst hq m
    exact DivisorReduction.orderAtLeastLocus_comap_of_smooth T hV Y q h hq m
  · exact DivisorReduction.isPullback_subschemeMapOfComap
  · exact DivisorReduction.smooth_of_isPullback
  · exact DivisorReduction.lowerIdealAfterBlowup_pullbackAlong_of_smooth exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le isBlowupAlongIdealSheaf_id_containedComponentsIdeal
  · exact DivisorReduction.lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_smooth exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le
      isBlowupAlongIdealSheaf_id_containedComponentsIdeal
  · exact DivisorReduction.containedComponentsIdeal_pullbackAlong_of_smooth hfacts

private theorem fieldBaseChangeCompatibility_of_divisorReductionTermination (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) :
    FieldBaseChangeCompatibility.{u} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T hV K inst f E' m
    exact orderAtLeastLocus_withBoundary_baseChange_eq_preimage T hV K f E' m
  · exact flat_fieldBaseChangeProjection
  · exact surjective_fieldBaseChangeProjection
  · exact containedComponentsIdeal_withBoundary_baseChange hfacts MarkedIdealWithBoundary.validOfSameNontrivialBoundary

private theorem divisorRestrictionFieldBaseChange : DivisorReduction.DivisorRestrictionFieldBaseChange.{u} := by
  refine ⟨comap_comap, comap_fieldBaseChangeProjection_ne_top, ?_, ?_, ?_, ?_, ?_⟩
  · intro T j hj K inst1 inst2 f E' hjE hD I₀ E₀ I₀' E₀' hI hE
    obtain ⟨E'', e, hs, hsu, h1, h2, h3, h4, h5, h6⟩ :=
      DivisorReduction.exists_smooth_surjective_to_restrictToBoundaryDivisor_baseChange T j hj K f E' hjE hD I₀ E₀ I₀' E₀' hI hE
    exact ⟨E'', e, hs, hsu, h1.symm, h2, h3, h4, h5, h6⟩
  · intro T K inst1 inst2 f E'
    exact lowerIdealWithoutBlowup_withBoundary_baseChange T K f E'
  · intro T j hj K inst1 inst2 f E' hBE htake hjE
    exact DivisorReduction.lowerBoundaryWithoutBlowup_baseChange_sameNontrivialBoundary T j hj K f E' hBE htake hjE
  · intro T hV hO j hj K inst1 inst2 f E' hBE hjE htake hV' hpre
    exact DivisorReduction.lowerIdealAfterBlowup_fieldBaseChange exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hV
      hO j hj K f E' hBE.symm hjE htake hV' hpre
  · intro T hV hO j hj K inst1 inst2 f E' hBE hjE htake hV' hpre
    exact DivisorReduction.lowerBoundaryAfterBlowup_fieldBaseChange exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hV hO
      j hj K f E' hBE.symm hjE htake hV' hpre

private theorem emptyPulledBackCenterCompatibility : DivisorReduction.EmptyPulledBackCenterCompatibility.{u} := by
  refine ⟨?_, ?_⟩
  · intro T hV hO j hj Y h htop
    exact DivisorReduction.comap_lowerIdealAfterBlowup_eq_comap_lowerIdealWithoutBlowup exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le
      isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hV hO j hj Y h htop
  · intro T hV j hj Y h htop
    exact DivisorReduction.comap_lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_eq_top exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le
      isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hV j hj Y h htop

private theorem pushedBlowupSequenceProperties_canonicalAlgorithmRules (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) :
    PushedBlowupSequenceProperties hres blowupPreservesNoetherian := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hV j hj
    exact DivisorReduction.isOpen_preimage_support_containedComponentsIdeal T j hj
      (DivisorReduction.preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj)
  · intro T inst j hj s hpr hmk
    exact DivisorReduction.ker_embeddingIntoAmbient_zero_eq_comap_isoObjZero hres blowupPreservesNoetherian T j hj s hpr hmk
  · intro T inst j hj hb s hpr hmk
    exact DivisorReduction.ker_embeddingIntoAmbient_zero_eq_comap_blowupMorphism hres blowupPreservesNoetherian T j hj hb s hpr
      hmk
  · intro T hV j hj S
    exact DivisorReduction.isSmoothDivisor_boundary_comap_isoObjZero T hV j hj S
  · intro T inst j hj s hpr hmk t ht
    exact DivisorReduction.boundaryLocus_subset_preimage_otherBoundaryLocus hres blowupPreservesNoetherian T j hj s hpr
      hmk t ht
  · intro T inst j hj hb s hpr hmk t ht
    exact DivisorReduction.boundaryLocus_subset_preimage_otherBoundaryLocus_succ hres blowupPreservesNoetherian T j hj hb s
      hpr hmk t ht
  · intro T hV
    exact DivisorReduction.one_le_mult_of_isAdmissible T hV
  · intro T hV hOB hbal j hj hpre hlow inst s hpr hmk t ht
    exact DivisorReduction.isSmoothDivisor_ker_embeddingIntoAmbient_of_eq_top hres blowupPreservesNoetherian T hV
      hOB hbal j hj hpre hlow s hpr hmk t ht
  · intro T hV hOB hbal j hj hne hb hlow inst s hpr hmk t ht
    exact DivisorReduction.isSmoothDivisor_ker_embeddingIntoAmbient hres blowupPreservesNoetherian
      orderAtComapOffExceptionalLocus T hV hOB j hj hb hlow s hpr hmk
      (fun t _ => DivisorReduction.embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι hres
        blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
        (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t) t ht
  · intro T inst j hj s hpr hmk t
    exact DivisorReduction.projectionToSpec_eq_comp_ambientMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk t
  · intro T inst j hj hb s hpr hmk t
    exact DivisorReduction.projectionToSpec_eq_comp_prependedAmbientSeq hres blowupPreservesNoetherian T j hj hb s hpr hmk t
  · intro X Y f inst I
    exact support_ker_comp_subset_support_ker I.subschemeι f
  · intro T hV j hj
    exact DivisorReduction.support_containedComponentsIdeal_subset_support_boundary T j hj

private theorem divisorReductionStepProperties_canonicalAlgorithmRules (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) :
    DivisorReductionStepProperties hres blowupPreservesNoetherian :=
  (divisorReductionProperties_of_blowupPreservesNoetherian hres blowupPreservesNoetherian).toDivisorReductionStepProperties

theorem divisorReductionHypotheses_canonicalAlgorithmRules (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) :
    DivisorReduction.DivisorReductionHypotheses hres := by
  have hstepProps := divisorReductionStepProperties_canonicalAlgorithmRules hres
  have hfacts := hstepProps.toDivisorReductionTerminationProperties
  refine
    { trivial_of_coSupport_empty := ?_
      baseChange := smoothPullbackCompatibility_of_divisorReductionTermination hres hfacts
      smoothImpliesFlat := ⟨fun X Y f hf => by have := hf; infer_instance⟩
      degenerateTransversal := emptyPulledBackCenterCompatibility
      fieldBaseChangeCompatibility := fieldBaseChangeCompatibility_of_divisorReductionTermination hres hfacts
      boundaryReindexingInvariance := DivisorReduction.boundaryReindexingInvariance
      fieldLower := divisorRestrictionFieldBaseChange
      divisorReduction := hstepProps
      pushedBlowupSequenceProperties := pushedBlowupSequenceProperties_canonicalAlgorithmRules hres }
  intro L j T hV hj Y q h inst hq E' hV' hne hempty B' hB'
  exact DivisorReductionEmptyOrderLocus.divisorFamily_isPullbackSequenceOfBlowups_of_orderAtLeastLocus_empty hres L j T hV hj Y q h hq E' hV'
    hne hempty B' hB'

end FunctorialResolution.EmbeddedResolution
