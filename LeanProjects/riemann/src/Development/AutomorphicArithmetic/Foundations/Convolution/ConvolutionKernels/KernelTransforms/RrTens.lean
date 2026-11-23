import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommInt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.rrTens :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure], Compat μ ν m →
      ∀ (β : TI K n) (e : TF K n), RR μ (tens β e) = Oinf μ ν β ∘L Ofin μ m e := by
  intro K _ _ n hn μ _ ν _ m _ hC β e
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
  have h1 := inner_integrated_ccToL1_eq (rightRegularRep (rationalGLOne K n) μ) μ (tens β e) w v
  have h2 := (UpperTheory.ConvolutionTheory.Tf.commInt (normOneGL K n) (archGroup K n) (AdelicGLn.FiniteAdelicGL K n) (LL μ)
    (rightRegularRep (rationalGLOne K n) μ) (archP K n) continuous_archP (MultiplicityOne.finProj K n)
    MultiplicityOne.continuous_finProj ν m β e).1 w v
  have h3 := hC β e (fun g => ⟪w, rightRegularRep (rationalGLOne K n) μ g v⟫_ℂ)
    (continuous_const.inner ((rightRegularRep (rationalGLOne K n) μ).continuous_orbit v))
  exact h1.trans (h3.trans h2.symm)
