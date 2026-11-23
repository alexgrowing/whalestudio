import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.Sobolev
import GroundTheory.AutomorphicForms.PartialDifferential.SobolevDuality

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

section MultiplierFourier

variable {m : E → ℂ} {C s t : ℝ}

theorem fourier_fourierMultiplierCLM_apply (m : E → ℂ) (u : 𝓢'(E, F)) (φ : 𝓢(E, ℂ)) :
    𝓕 (fourierMultiplierCLM F m u) φ = 𝓕 u (SchwartzMap.smulLeftCLM ℂ m φ) := by
  rw [fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq, smulLeftCLM_apply_apply]

theorem fourierFun_multiplier (hm : m.HasTemperateGrowth)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) (u : SobolevSpace E F s) :
    fourierFun (SobolevSpace.multiplier hm hC u) =ᵐ[volume] (fun ξ ↦ m ξ • fourierFun u ξ) ∧
      ‖SobolevSpace.multiplier hm hC u‖ ^ 2 =
        ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ t * ‖m ξ • fourierFun u ξ‖ ^ 2 := by
  have hmem : MemLp (fun ξ ↦ weight t ξ • (m ξ • fourierFun u ξ)) 2 (volume : Measure E) := by
    refine (memLp_smul_of_bounded (hasTemperateGrowth_mul_weight hm (t - s)) (bounded_mul_weight hC)
      (𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E))).congr_norm ?_ ?_
    · exact (weight_hasTemperateGrowth t).1.continuous.aestronglyMeasurable.smul
        (hm.1.continuous.aestronglyMeasurable.smul (fourierFun_aestronglyMeasurable u))
    · refine ae_of_all _ fun ξ ↦ ?_
      have e : m ξ * weight (t - s) ξ * weight s ξ = weight t ξ * m ξ := by
        rw [mul_assoc, weight_mul_weight, sub_add_cancel, mul_comm]
      rw [← weight_smul_fourierFun]
      simp only [smul_smul]
      rw [e]
  have hrep : ∀ φ : 𝓢(E, ℂ), 𝓕 (SobolevSpace.toDistribution (SobolevSpace.multiplier hm hC u)) φ =
      ∫ ξ, φ ξ • (m ξ • fourierFun u ξ) := by
    intro φ
    rw [SobolevSpace.toDistribution_multiplier, fourier_fourierMultiplierCLM_apply,
      fourier_apply_eq_integral]
    congr 1; ext ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply hm, smul_smul, smul_eq_mul, mul_comm]
  have h := norm_sq_eq_integral_of_fourier _ _ hmem hrep
  exact ⟨h.1.symm, h.2⟩

theorem integrable_weight_mul_norm_sq_fourierFun (u : SobolevSpace E F s) :
    Integrable (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ s * ‖fourierFun u ξ‖ ^ 2) (volume : Measure E) := by
  have h := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1
    (Lp.memLp (𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E)))
  refine h.congr (ae_of_all _ fun ξ ↦ ?_)
  simp only
  rw [← weight_smul_fourierFun, norm_smul, norm_weight, mul_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  norm_num

theorem bound_of_le {m : E → ℂ} {M : ℝ} (hM : ∀ ξ, ‖m ξ‖ ≤ M) (ξ : E) :
    ‖m ξ‖ ≤ M * (1 + ‖ξ‖ ^ 2) ^ ((s - s) / 2) := by
  rw [sub_self, zero_div, Real.rpow_zero, mul_one]; exact hM ξ

end MultiplierFourier

section Convolution

variable (E) in

def reflect : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := E)).toContinuousLinearEquiv

variable (F) in

def convolution (ψ : 𝓢(E, ℂ)) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  PointwiseConvergenceCLM.precomp F
    (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (reflect E ψ))

theorem convolution_apply_apply (ψ : 𝓢(E, ℂ)) (u : 𝓢'(E, F)) (φ : 𝓢(E, ℂ)) :
    convolution F ψ u φ =
      u (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (reflect E ψ) φ) := rfl

theorem fourier_reflect (ψ : 𝓢(E, ℂ)) (x : E) : 𝓕 (reflect E ψ) x = 𝓕 ψ (-x) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  exact Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) ψ x

theorem convolution_reflect_eq (ψ φ : 𝓢(E, ℂ)) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (reflect E ψ) φ =
      𝓕 (SchwartzMap.smulLeftCLM ℂ ⇑(𝓕 ψ : 𝓢(E, ℂ)) (𝓕⁻ φ)) := by
  apply SchwartzMap.ext; intro x
  have hψ := (𝓕 ψ : 𝓢(E, ℂ)).hasTemperateGrowth
  simp only [SchwartzMap.convolution, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply, fourierInvCLM_apply, fourierCLM_apply]
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, Real.fourierInv_eq_fourier_comp_neg]
  have h : (fun y ↦ (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 (reflect E ψ)) (𝓕 φ))
      (-y)) = (⇑(SchwartzMap.smulLeftCLM ℂ ⇑(𝓕 ψ : 𝓢(E, ℂ)) (𝓕⁻ φ)) : E → ℂ) := by
    funext y
    rw [SchwartzMap.pairing_apply_apply, SchwartzMap.smulLeftCLM_apply_apply hψ, fourier_reflect,
      neg_neg, ContinuousLinearMap.mul_apply', smul_eq_mul, SchwartzMap.fourierInv_coe,
      Real.fourierInv_eq_fourier_neg, SchwartzMap.fourier_coe]
    rfl
  exact congrArg (fun g : E → ℂ ↦ 𝓕 g x) h

theorem convolution_eq_fourierMultiplierCLM (ψ : 𝓢(E, ℂ)) (u : 𝓢'(E, F)) :
    convolution F ψ u = fourierMultiplierCLM F ⇑(𝓕 ψ : 𝓢(E, ℂ)) u := by
  ext φ
  rw [convolution_apply_apply, convolution_reflect_eq, fourierMultiplierCLM_apply_apply]

end Convolution

section Mollifier

theorem norm_fourier_le_integral (ψ : 𝓢(E, ℂ)) (ξ : E) :
    ‖(𝓕 ψ : 𝓢(E, ℂ)) ξ‖ ≤ ∫ x, ‖ψ x‖ := by
  rw [SchwartzMap.fourier_coe]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem exists_norm_le_weight (χ : 𝓢(E, ℂ)) (r : ℝ) :
    ∃ C, ∀ ξ : E, ‖χ ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
  set n : ℕ := ⌈-r / 2⌉₊
  refine ⟨2 ^ n * (SchwartzMap.seminorm ℂ 0 0 χ + SchwartzMap.seminorm ℂ (2 * n) 0 χ), fun ξ ↦ ?_⟩
  have h0 : ‖χ ξ‖ ≤ SchwartzMap.seminorm ℂ 0 0 χ := by
    have := SchwartzMap.le_seminorm ℂ 0 0 χ ξ
    simpa [norm_iteratedFDeriv_zero] using this
  have h1 : ‖ξ‖ ^ (2 * n) * ‖χ ξ‖ ≤ SchwartzMap.seminorm ℂ (2 * n) 0 χ := by
    have := SchwartzMap.le_seminorm ℂ (2 * n) 0 χ ξ
    simpa [norm_iteratedFDeriv_zero] using this
  have hb : (1 : ℝ) ≤ 1 + ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg ‖ξ‖]
  have hpow : (1 + ‖ξ‖ ^ 2) ^ n ≤ 2 ^ n * (1 + (‖ξ‖ ^ 2) ^ n) := by
    rcases le_total (‖ξ‖ ^ 2) 1 with h | h
    · calc (1 + ‖ξ‖ ^ 2) ^ n ≤ 2 ^ n := by
            apply pow_le_pow_left₀ (by positivity); linarith
        _ ≤ 2 ^ n * (1 + (‖ξ‖ ^ 2) ^ n) := by
            have : 0 ≤ (‖ξ‖ ^ 2) ^ n := by positivity
            nlinarith [pow_pos (two_pos (α := ℝ)) n]
    · calc (1 + ‖ξ‖ ^ 2) ^ n ≤ (2 * ‖ξ‖ ^ 2) ^ n := by
            apply pow_le_pow_left₀ (by positivity); linarith
        _ = 2 ^ n * (‖ξ‖ ^ 2) ^ n := by rw [mul_pow]
        _ ≤ 2 ^ n * (1 + (‖ξ‖ ^ 2) ^ n) := by gcongr; linarith
  have key : (1 + ‖ξ‖ ^ 2) ^ n * ‖χ ξ‖ ≤
      2 ^ n * (SchwartzMap.seminorm ℂ 0 0 χ + SchwartzMap.seminorm ℂ (2 * n) 0 χ) := by
    calc (1 + ‖ξ‖ ^ 2) ^ n * ‖χ ξ‖ ≤ 2 ^ n * (1 + (‖ξ‖ ^ 2) ^ n) * ‖χ ξ‖ := by gcongr
      _ = 2 ^ n * (‖χ ξ‖ + ‖ξ‖ ^ (2 * n) * ‖χ ξ‖) := by rw [pow_mul]; ring
      _ ≤ _ := by gcongr
  have hpos : 0 < (1 + ‖ξ‖ ^ 2) ^ n := by positivity
  have hexp : (1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ)) ≤ (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le hb
    have := Nat.le_ceil (-r / 2)
    linarith
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast] at hexp
  calc ‖χ ξ‖ = ((1 + ‖ξ‖ ^ 2) ^ n * ‖χ ξ‖) * ((1 + ‖ξ‖ ^ 2) ^ n)⁻¹ := by
        field_simp
    _ ≤ 2 ^ n * (SchwartzMap.seminorm ℂ 0 0 χ + SchwartzMap.seminorm ℂ (2 * n) 0 χ) *
        ((1 + ‖ξ‖ ^ 2) ^ n)⁻¹ := by gcongr
    _ ≤ _ := by
        gcongr

namespace SobolevSpace

variable {s : ℝ}

@[simp] theorem toDistribution_sub (u v : SobolevSpace E F s) :
    toDistribution (u - v) = toDistribution u - toDistribution v := rfl

def convolutionCLM (ψ : 𝓢(E, ℂ)) : SobolevSpace E F s →L[ℂ] SobolevSpace E F s :=
  multiplier (𝓕 ψ : 𝓢(E, ℂ)).hasTemperateGrowth (bound_of_le (norm_fourier_le_integral ψ))

@[simp] theorem toDistribution_convolutionCLM (ψ : 𝓢(E, ℂ)) (u : SobolevSpace E F s) :
    toDistribution (convolutionCLM ψ u) = convolution F ψ (toDistribution u) := by
  rw [convolution_eq_fourierMultiplierCLM]; rfl

end SobolevSpace

def mollifier (ψ : 𝓢(E, ℂ)) (ε : ℝ) : 𝓢(E, ℂ) :=
  if h : ε = 0 then ψ else
    ((|ε| ^ Module.finrank ℝ E)⁻¹ : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (LinearEquiv.smulOfNeZero ℝ E ε⁻¹ (inv_ne_zero h)).toContinuousLinearEquiv ψ

end Mollifier

end

end GroundTheory.Automorphic.Sobolev
