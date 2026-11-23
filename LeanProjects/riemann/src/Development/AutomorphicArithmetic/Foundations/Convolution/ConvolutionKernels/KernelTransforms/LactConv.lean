import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LactSpec
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.ConvL
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RightDerivConvComm
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CenterC

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

section SlopeTestRemainingChoices

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G) [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [BorelSpace G] [IsFiniteMeasureOnCompacts μ]

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
private theorem lactConv_integrable (f g : CompactlySupportedContinuousMap G ℂ) (x : G) :
    Integrable (fun a => f a * g (a⁻¹ * x)) μ := by
  have hc : Continuous fun a => f a * g (a⁻¹ * x) :=
    (map_continuous f).mul ((map_continuous g).comp (continuous_inv.mul continuous_const))
  exact hc.integrable_of_hasCompactSupport (f.hasCompactSupport.mul_right)

private theorem lactConv_left (f f' g : CompactlySupportedContinuousMap G ℂ) (c : ℂ) :
    conv μ (f + c • f') g = conv μ f g + c • conv μ f' g := by
  ext x
  simp only [conv_apply, CompactlySupportedContinuousMap.add_apply, CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_add (lactConv_integrable μ f g x) ((lactConv_integrable μ f' g x).const_mul c)]
  congr 1
  funext a
  ring

private theorem lactConv_right (f g g' : CompactlySupportedContinuousMap G ℂ) (c : ℂ) :
    conv μ f (g + c • g') = conv μ f g + c • conv μ f g' := by
  ext x
  simp only [conv_apply, CompactlySupportedContinuousMap.add_apply, CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_add (lactConv_integrable μ f g x) ((lactConv_integrable μ f g' x).const_mul c)]
  congr 1
  funext a
  ring

end SlopeTestRemainingChoices

private theorem lactConv_split {K : Type} [Field K] [NumberField K] {n : ℕ} (β : TI K n) (hβ : SmoothT β) (a b : UEnv K n) :
    lact ((1 : ℂ) ⊗ₜ[ℝ] a + Complex.I ⊗ₜ[ℝ] b) β = lact ((1 : ℂ) ⊗ₜ[ℝ] a) β + Complex.I • lact ((1 : ℂ) ⊗ₜ[ℝ] b) β := by
  obtain ⟨_, -, -, -, h4, h5, -⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n β hβ
  have e : (Complex.I ⊗ₜ[ℝ] b : UC K n) = Complex.I • ((1 : ℂ) ⊗ₜ[ℝ] b) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [(h4 _ _).2, e, (h5 _ _).1]

theorem UpperTheory.ConvolutionTheory.Tf.lactConv :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β₁ β₂ : TI K n), SmoothT β₁ →
      SmoothT (conv ν β₁ β₂) ∧ (∀ u, lact u (conv ν β₁ β₂) = conv ν (lact u β₁) β₂) ∧
      (IsTotallyComplex K → SmoothT β₂ → ∀ z ∈ Subalgebra.center ℂ (UC K n), conv ν (lact z β₁) β₂ = conv ν β₁ (lact z β₂)) := by
  intro K _ _ n ν _ β₁ β₂ hβ₁
  obtain ⟨h₁, -, -, -, -, -, -, e₁⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n β₁ hβ₁
  obtain ⟨h₁₂, hL⟩ := UpperTheory.ConvolutionTheory.Tf.convL K n ν β₁ β₂ h₁
  have hs : SmoothT (conv ν β₁ β₂) := by
    have h := (UpperTheory.ConvolutionTheory.Tf.invSmooth K n _ h₁₂).1
    simp only [inv_inv] at h
    exact h
  refine ⟨hs, ?_, ?_⟩
  · obtain ⟨h', -, -, -, -, -, -, e'⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n _ hs
    have key : ∀ a : UEnv K n, lact ((1 : ℂ) ⊗ₜ[ℝ] a) (conv ν β₁ β₂) = conv ν (lact ((1 : ℂ) ⊗ₜ[ℝ] a) β₁) β₂ := by
      intro a
      ext x
      rw [e', hL, conv_apply]
      simp only [e₁]
    intro u
    obtain ⟨a, b, rfl⟩ := (UpperTheory.ConvolutionTheory.Tf.centerC (UEnv K n) u).1
    rw [lactConv_split _ hs, lactConv_split _ hβ₁, lactConv_left, key, key]
  · intro hK hβ₂ z hz
    obtain ⟨h₂, -, -, -, -, -, -, e₂⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n β₂ hβ₂
    have key : ∀ a ∈ Subalgebra.center ℝ (UEnv K n),
        conv ν (lact ((1 : ℂ) ⊗ₜ[ℝ] a) β₁) β₂ = conv ν β₁ (lact ((1 : ℂ) ⊗ₜ[ℝ] a) β₂) := by
      intro a ha
      ext x
      rw [conv_apply, conv_apply]
      simp only [e₁, e₂]
      exact UpperTheory.ConvolutionTheory.Tf.convZ K n ν β₁ β₂ h₁ h₂ a ha x
    obtain ⟨⟨a, b, hab⟩, hc⟩ := UpperTheory.ConvolutionTheory.Tf.centerC (UEnv K n) z
    obtain ⟨ha, hb⟩ := (hc a b hab).1 hz
    rw [hab, lactConv_split _ hβ₁, lactConv_split _ hβ₂, lactConv_left, lactConv_right, key a ha, key b hb]
