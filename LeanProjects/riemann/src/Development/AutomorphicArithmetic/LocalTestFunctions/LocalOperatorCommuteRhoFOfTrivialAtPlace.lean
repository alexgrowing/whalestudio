import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.PrjFix
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HomConv
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.localOperator_commute_rhoF_of_trivial_at_place :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K)
          [MeasurableSpace (Gw n w)] (mw : Measure (Gw n w)) (φ : Gw n w → ℂ) (T : LL μ →L[ℂ] LL μ), IsOloc μ w mw φ T →
          ∀ h : AdelicGLn.FiniteAdelicGL K n, finAt w (finEmb K n h) = 1 → Commute T (rhoF μ h) := by
  intro K _ _ n μ _ w _ mw φ T hT h hh
  obtain ⟨-, -, -, -, -, hmul, -, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥
  have hc := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.2 h hh
  have hcomm : ∀ (g : Gw n w) (v : LL μ), rhoL μ w g (rhoF μ h v) = rhoF μ h (rhoL μ w g v) := by
    intro g v
    have e : rhoF μ (AdelicGLn.localEmbedding w g * h) = rhoF μ (h * AdelicGLn.localEmbedding w g) := by
      rw [hc g]
    rw [hmul, hmul] at e
    exact congrArg (fun S : LL μ →L[ℂ] LL μ => S v) e
  have key : ∀ u v : LL μ, ⟪u, T (rhoF μ h v)⟫_ℂ = ⟪u, rhoF μ h (T v)⟫_ℂ := by
    intro u v
    rw [← ContinuousLinearMap.adjoint_inner_left (rhoF μ h) (T v) u, hT u, hT]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show φ g * ⟪u, rhoL μ w g (rhoF μ h v)⟫_ℂ = φ g * ⟪ContinuousLinearMap.adjoint (rhoF μ h) u, rhoL μ w g v⟫_ℂ
    rw [ContinuousLinearMap.adjoint_inner_left, hcomm]
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  exact key u v
