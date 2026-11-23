import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensOp
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactorAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.SideE
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CompatEx
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RrTens
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.PrjFix
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LeftSm
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.tensAmp :
    TensAmp := by
  intro K _ _ _ n hn μ _ 𝔞 φ hφ
  obtain ⟨m, hm, hC⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ 𝔞.ν
  have hUo := 𝔞.isOpen
  have hUc : IsCompact (𝔞.U : Set (FA K n)) :=
    (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hUo) 𝔞.le
  have hpos : 0 < m.real (𝔞.U : Set (FA K n)) :=
    ENNReal.toReal_pos (hUo.measure_pos m ⟨1, 𝔞.U.one_mem⟩).ne' hUc.measure_lt_top.ne
  have hne : ((m.real (𝔞.U : Set (FA K n)) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
  refine ⟨⟨m.real (𝔞.U : Set (FA K n)), hpos, fun Θ hΘ hfix x => ?_, ?_⟩, fun c => ?_⟩
  · rw [hC 𝔞.a₀ φ (fun g => Θ (x * g)) (hΘ.comp (continuous_const.mul continuous_id)), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    have h1 : ∀ h : FA K n, 𝔞.a₀ a * φ h * Θ (x * (archP K n a * MultiplicityOne.finProj K n h)) =
        (𝔞.U : Set (FA K n)).indicator (fun _ => 𝔞.a₀ a * Θ (x * archP K n a)) h := by
      intro h
      by_cases hh : h ∈ (𝔞.U : Set (FA K n))
      · rw [hφ, Set.indicator_of_mem hh, Set.indicator_of_mem hh, ← mul_assoc x, hfix h hh]
        simp
      · rw [hφ, Set.indicator_of_notMem hh, Set.indicator_of_notMem hh]
        simp
    simp only [h1]
    rw [integral_indicator_const _ hUo.measurableSet, Complex.real_smul]
  · obtain ⟨e, he, hO⟩ := UpperTheory.ConvolutionTheory.Tf.prjFix K n μ m 𝔞.U hUo hUc
    have h2 : φ = ((m.real (𝔞.U : Set (FA K n)) : ℝ) : ℂ) • e := by
      ext h
      rw [CompactlySupportedContinuousMap.smul_apply, he, hφ]
      by_cases hh : h ∈ (𝔞.U : Set (FA K n))
      · rw [Set.indicator_of_mem hh, Set.indicator_of_mem hh, smul_eq_mul, mul_inv_cancel₀ hne]
        rfl
      · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem hh, smul_zero]
    have h3 := UpperTheory.ConvolutionTheory.Tf.rrTens K n hn μ 𝔞.ν m hC 𝔞.a₀ φ
    have h4 := ((UpperTheory.ConvolutionTheory.Tf.opAlg K n μ 𝔞.ν m).2.2.1 ((m.real (𝔞.U : Set (FA K n)) : ℝ) : ℂ) 𝔞.a₀ e).2
    rw [← h2, hO] at h4
    rw [h4, ContinuousLinearMap.comp_smul] at h3
    exact h3
  · rw [← ((UpperTheory.ConvolutionTheory.Tf.tensApply K n hn 𝔞.a₀ φ).2.2.2.2 c).2]
    refine (UpperTheory.ConvolutionTheory.Tf.leftSm K n hn 𝔞.a₀ (c • φ)).1 𝔞.smooth ⟨𝔞.U, hUo, fun u hu h => ?_⟩
    rw [CompactlySupportedContinuousMap.smul_apply, CompactlySupportedContinuousMap.smul_apply, hφ, hφ]
    by_cases hh : h ∈ (𝔞.U : Set (FA K n))
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem (show u * h ∈ (𝔞.U : Set (FA K n)) from 𝔞.U.mul_mem hu hh)]
      rfl
    · rw [Set.indicator_of_notMem hh,
        Set.indicator_of_notMem (show u * h ∉ (𝔞.U : Set (FA K n)) from fun h' => hh ((𝔞.U.mul_mem_cancel_left hu).1 h'))]
