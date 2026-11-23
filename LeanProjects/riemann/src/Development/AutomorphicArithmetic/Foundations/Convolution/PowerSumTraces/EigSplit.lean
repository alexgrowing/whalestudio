import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.TwistedTraces.CfcApplyOfEigenvector
import Development.AutomorphicArithmetic.TwistedTraces.EigInFiniteAboveOfIsCompactOperator
import Development.AutomorphicArithmetic.TwistedTraces.ExistsHilbertBasisPrjEigenvectorsOfIsCompactOper
import Development.AutomorphicArithmetic.TwistedTraces.NormTraceCompLeMulTraceNorm
import Development.AutomorphicArithmetic.TwistedTraces.TrOnSubSumEqTraceCompCompression
import Development.AutomorphicArithmetic.TwistedTraces.PrjEigInOfEigenvectorPrj

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

theorem UpperTheory.ConvolutionTheory.C.eigSplit :
    UpperTheory.ConvolutionTheory.C.EigSplit := by
  intro H _ _ _ W A hW hA hinv hK η hη
  have hsa : IsSelfAdjoint A := isSelfAdjoint_of_nonneg hA
  obtain ⟨hfin, hfd⟩ := UpperTheory.eigIn_finite_above_of_isCompactOperator H W A hW hsa hinv hK η hη
  obtain ⟨s, b, hb⟩ := UpperTheory.exists_hilbertBasis_prj_eigenvectors_of_isCompactOperator H W A hW hsa hinv hK
  have hS : ∀ x, x ∈ hfin.toFinset ↔ η < x ∧ eigIn W A x ≠ ⊥ := fun x => by simp
  refine ⟨hfin.toFinset, hS, fun x hx => hfd x ((hS x).1 hx).1, fun φ c T hφ hc hφc hT => ?_⟩
  rw [UpperTheory.trOn_sub_sum_eq_trace_comp_compression H W (eigIn W A) hfin.toFinset (fun x => (φ x : ℂ)) (cfc φ A) T (fun x => inf_le_left) hT]
  have hmem : ∀ v, prj W v ∈ W := fun v => by
    have h : prj W v ∈ W.topologicalClosure := Submodule.starProjection_apply_mem _ v
    rwa [hW.submodule_topologicalClosure_eq] at h
  have hPP : ∀ v, prj W (prj W v) = prj W v := fun v =>
    Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ v)
  refine UpperTheory.norm_trace_comp_le_mul_traceNorm H s b _ _ c hc hT fun i => ?_
  obtain ⟨μ, hμ⟩ := hb i
  have hF := UpperTheory.cfc_apply_of_eigenvector H A hsa φ hφ μ _ hμ
  have hD : (prj W ∘L cfc φ A ∘L prj W - ∑ x ∈ hfin.toFinset, (φ x : ℂ) • prj (eigIn W A x)) (b i) =
      (if μ ∈ hfin.toFinset then 0 else (φ μ : ℂ)) • prj W (b i) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, hF, map_smul, hPP, UpperTheory.prj_eigIn_of_eigenvector_prj H W A hW hsa (b i) μ _ hμ, smul_ite, smul_zero,
      Finset.sum_ite_eq']
    split_ifs <;> simp
  rw [hD]
  by_cases h0 : prj W (b i) = 0
  · exact ⟨0, by simpa using hc, by simp [h0]⟩
  refine ⟨if μ ∈ hfin.toFinset then 0 else (φ μ : ℂ), ?_, by simp only [map_smul, ContinuousLinearMap.comp_apply, hPP]⟩
  split_ifs with hm
  · simpa using hc
  have hne : eigIn W A μ ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨_, ⟨hmem _, Module.End.mem_eigenspace_iff.2 hμ⟩, h0⟩
  have hle : μ ≤ η := not_lt.1 fun h => hm ((hS μ).2 ⟨h, hne⟩)
  have hge : 0 ≤ μ := by
    have h1 := ((ContinuousLinearMap.nonneg_iff_isPositive A).1 hA).re_inner_nonneg_right (prj W (b i))
    rw [hμ, inner_smul_right, inner_self_eq_norm_sq_to_K] at h1
    have h2 : 0 < ‖prj W (b i)‖ ^ 2 := by positivity
    have h3 : 0 ≤ μ * ‖prj W (b i)‖ ^ 2 := by
      have : RCLike.re ((μ : ℂ) * ((‖prj W (b i)‖ : ℝ) : ℂ) ^ 2) = μ * ‖prj W (b i)‖ ^ 2 := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]; rfl
      rw [← this]; exact h1
    exact nonneg_of_mul_nonneg_left h3 h2
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hφc μ ⟨hge, hle⟩
