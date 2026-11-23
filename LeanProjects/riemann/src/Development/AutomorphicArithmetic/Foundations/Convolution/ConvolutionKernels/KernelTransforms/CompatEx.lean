import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensMeas
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.compatEx :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n →
      (∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure], ∃ (ν : Measure (archGroup K n)) (_ : ν.IsHaarMeasure), Compat μ ν m) ∧
      (∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure], ∃ (m : Measure (AdelicGLn.FiniteAdelicGL K n)) (_ : m.IsHaarMeasure), Compat μ ν m) ∧
      ∀ (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure], ∃ (μ : Measure (normOneGL K n)) (_ : μ.IsHaarMeasure), Compat μ ν m := by
  intro K _ _ n hn
  have main : ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
      (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure], ∃ c : NNReal, c ≠ 0 ∧
      Compat μ (c • ν) m ∧ Compat μ ν (c • m) ∧ Compat (c⁻¹ • μ) ν m := by
    intro μ _ ν _ m _
    obtain ⟨c, hc, h⟩ := UpperTheory.ConvolutionTheory.Tf.tensMeas K n hn μ ν m
    lift c to NNReal using hc.le
    have h' : ∀ (β : TI K n) (e : TF K n) (Θ : normOneGL K n → ℂ), Continuous Θ → ∫ x, tens β e x * Θ x ∂μ =
        ((c : ℝ) : ℂ) * ∫ a, ∫ y, β a * e y * Θ (archP K n a * MultiplicityOne.finProj K n y) ∂m ∂ν := fun β e Θ hΘ => by
      rw [← h β e Θ hΘ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [(UpperTheory.ConvolutionTheory.Tf.tensApply K n hn β e).1 x]
      rfl
    have hc0 : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    refine ⟨c, by exact_mod_cast hc.ne', fun β e Θ hΘ => ?_, fun β e Θ hΘ => ?_, fun β e Θ hΘ => ?_⟩
    · rw [h' β e Θ hΘ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    · rw [h' β e Θ hΘ, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      dsimp only
      rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    · rw [integral_smul_nnreal_measure, h' β e Θ hΘ, NNReal.smul_def, Complex.real_smul, ← mul_assoc, NNReal.coe_inv,
        Complex.ofReal_inv, inv_mul_cancel₀ hc0, one_mul]
  refine ⟨fun μ _ m _ => ?_, fun μ _ ν _ => ?_, fun ν _ m _ => ?_⟩
  · obtain ⟨c, hc, h, -, -⟩ := main μ Measure.haar m
    exact ⟨_, Measure.IsHaarMeasure.nnreal_smul _ hc, h⟩
  · obtain ⟨c, hc, -, h, -⟩ := main μ ν Measure.haar
    exact ⟨_, Measure.IsHaarMeasure.nnreal_smul _ hc, h⟩
  · obtain ⟨c, hc, -, -, h⟩ := main Measure.haar ν m
    exact ⟨_, Measure.IsHaarMeasure.nnreal_smul _ (inv_ne_zero hc), h⟩
