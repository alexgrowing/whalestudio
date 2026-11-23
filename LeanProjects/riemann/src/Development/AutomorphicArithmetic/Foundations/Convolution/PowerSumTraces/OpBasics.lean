import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

private theorem compact_of_restrict {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule ℂ H) (hW : IsClosed (W : Set H)) (A : H →L[ℂ] H) (T : W →L[ℂ] W)
    (hT : IsCompactOperator T) (h : W.subtypeL ∘L T = A ∘L W.subtypeL) :
    IsCompactOperator (A ∘L prj W) := by
  have hmem : ∀ v, prj W v ∈ W := fun v => by
    have h1 : prj W v ∈ W.topologicalClosure := W.topologicalClosure.starProjection_apply_mem v
    rwa [hW.submodule_topologicalClosure_eq] at h1
  have e : A ∘L prj W = W.subtypeL ∘L (T ∘L (prj W).codRestrict W hmem) := by
    rw [← ContinuousLinearMap.comp_assoc, h]
    rfl
  rw [e]
  exact (hT.comp_clm ((prj W).codRestrict W hmem)).clm_comp W.subtypeL

theorem UpperTheory.ConvolutionTheory.C.opBasics :
    UpperTheory.ConvolutionTheory.C.OpBasics := by
  intro K _ _ n μ _ f
  refine ⟨fun V hV v hv => ?_, fun v hv => ?_, ?_⟩
  · exact UnitaryRep.IsInvariant.integrated_mem _ μ hV.closed hV.inv _ hv
  · exact UnitaryRep.IsInvariant.integrated_mem _ μ (isClosed_cuspidalL2 μ)
      (isInvariant_cuspidalL2 μ) _ hv
  · exact compact_of_restrict _ (isClosed_cuspidalL2 μ) _ _ (isCompactOperator_cuspRep μ f)
      (subtypeL_comp_integrated μ _)
