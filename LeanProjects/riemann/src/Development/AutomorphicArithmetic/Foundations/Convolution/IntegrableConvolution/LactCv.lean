import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LactLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LactConv

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1

private theorem cv_eq_conv {K : Type} [Field K] [NumberField K] {n : ℕ} (ν : Measure (archGroup K n))
    [ν.IsHaarMeasure] (α β : TI K n) (g : archGroup K n) : cv ν α β g = conv ν α β g := by
  rw [conv_apply]
  rfl

private theorem leftFin_cv {K : Type} [Field K] [NumberField K] {n : ℕ} (ν : Measure (archGroup K n))
    [ν.IsHaarMeasure] (α β γ : TI K n) (hγ : ∀ g, γ g = cv ν α β g) (hα : LeftFin α) : LeftFin γ := by
  unfold LeftFin at hα ⊢
  set W := Submodule.span ℂ (Set.range fun k : archCompact K n => fun g : archGroup K n => α ((k : archGroup K n) * g))
    with hW
  have hW' : ∀ f ∈ W, Continuous f ∧ HasCompactSupport f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨(map_continuous α).comp (continuous_const.mul continuous_id),
        α.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft (k : archGroup K n))⟩
    | zero => exact ⟨continuous_zero, HasCompactSupport.zero⟩
    | add x y _ _ hx hy => exact ⟨hx.1.add hy.1, hx.2.add hy.2⟩
    | smul c x _ hx => exact ⟨hx.1.const_smul c, hx.2.smul_left⟩
  have hint : ∀ f ∈ W, ∀ g : archGroup K n, Integrable (fun y => f y * β (y⁻¹ * g)) ν := by
    intro f hf g
    obtain ⟨h1, h2⟩ := hW' f hf
    exact (h1.mul ((map_continuous β).comp (continuous_inv.mul continuous_const))).integrable_of_hasCompactSupport
      h2.mul_right
  let T : W →ₗ[ℂ] (archGroup K n → ℂ) :=
    { toFun := fun f g => ∫ y, (f : archGroup K n → ℂ) y * β (y⁻¹ * g) ∂ν
      map_add' := by
        intro f f'
        funext g
        simp only [Submodule.coe_add, Pi.add_apply, add_mul]
        exact integral_add (hint f f.2 g) (hint f' f'.2 g)
      map_smul' := by
        intro c f
        funext g
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ }
  have hle : Submodule.span ℂ (Set.range fun k : archCompact K n => fun g : archGroup K n => γ ((k : archGroup K n) * g)) ≤
      LinearMap.range T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    refine ⟨⟨fun g => α ((k : archGroup K n) * g), Submodule.subset_span ⟨k, rfl⟩⟩, ?_⟩
    funext g
    change ∫ y, α ((k : archGroup K n) * y) * β (y⁻¹ * g) ∂ν = γ ((k : archGroup K n) * g)
    rw [hγ, cv, ← integral_mul_left_eq_self (μ := ν)
      (fun y => α y * β (y⁻¹ * ((k : archGroup K n) * g))) (k : archGroup K n)]
    congr 1
    funext y
    simp [mul_assoc]
  exact Submodule.finiteDimensional_of_le hle

theorem UpperTheory.ConvolutionTheory.L1.lactCv :
    UpperTheory.ConvolutionTheory.L1.LactCv := by
  intro K _ _ _ n ν _ α β γ hα hγ
  have e : γ = conv ν α β := by
    ext g
    rw [hγ, cv_eq_conv]
  obtain ⟨hs, hu, hz⟩ := UpperTheory.ConvolutionTheory.Tf.lactConv K n ν α β hα
  refine ⟨e ▸ hs, leftFin_cv ν α β γ hγ, fun u g => ?_, fun hβ z hz' g => ?_⟩
  · rw [e, hu, ← cv_eq_conv]
  · rw [e, hu, hz inferInstance hβ z hz', ← cv_eq_conv]
