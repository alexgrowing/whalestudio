import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.PrjFix
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HomConv
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.integrated_rightRegular_eq_localOperator :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K)
          [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (mw : Measure (Gw n w)) [mw.IsHaarMeasure]
          (ψ : CompactlySupportedContinuousMap (Gw n w) ℂ) (T : LL μ →L[ℂ] LL μ), IsOloc μ w mw ψ T →
          (((rightRegularRep (rationalGLOne K n) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj).compHom
            (AdelicGLn.localEmbedding w) (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1).integrated mw (UnitaryRep.ccToL1 mw ψ) = T := by
  intro K _ _ n μ _ w _ _ mw _ ψ T h
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  rw [UnitaryRep.inner_integrated, h u v]
  refine integral_congr_ae ((RightCosetSpace.coeFn_compactSupportToL1 mw ψ).mono fun g hg => ?_)
  have hr : (((rightRegularRep (rationalGLOne K n) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj).compHom
      (AdelicGLn.localEmbedding w) (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1) g = rhoL μ w g := by
    simp only [UnitaryRep.compHom_apply]
    rfl
  simp only [hr]
  exact congrArg (· * ⟪u, rhoL μ w g v⟫_ℂ) hg
