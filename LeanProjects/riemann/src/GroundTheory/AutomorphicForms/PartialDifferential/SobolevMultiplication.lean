import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.SobolevRellich
import GroundTheory.AutomorphicForms.PartialDifferential.SobolevEmbedding

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem lintegral_conv_sq_le {K G : E → ℝ≥0∞} (hK : Measurable K) (hG : Measurable G) (ξ : E) :
    (∫⁻ η, K (ξ - η) * G η) ^ 2 ≤ (∫⁻ ζ, K ζ) * ∫⁻ η, K (ξ - η) * G η ^ 2 := by
  have hK' : Measurable fun η : E ↦ K (ξ - η) := hK.comp (measurable_const.sub measurable_id)
  have h := L2Kernel.lintegral_mul_sq_le (volume : Measure E)
    (f := fun η ↦ K (ξ - η) ^ (1 / 2 : ℝ)) (g := fun η ↦ K (ξ - η) ^ (1 / 2 : ℝ) * G η)
    (hK'.pow_const _).aemeasurable ((hK'.pow_const _).mul hG).aemeasurable
  have e2 : ∀ η, (K (ξ - η) ^ (1 / 2 : ℝ)) ^ 2 = K (ξ - η) := by
    intro η; rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have e1 : ∀ η, K (ξ - η) ^ (1 / 2 : ℝ) * (K (ξ - η) ^ (1 / 2 : ℝ) * G η) = K (ξ - η) * G η := by
    intro η; rw [← mul_assoc, ← pow_two, e2]
  have e3 : ∀ η, (K (ξ - η) ^ (1 / 2 : ℝ) * G η) ^ 2 = K (ξ - η) * G η ^ 2 := by
    intro η; rw [mul_pow, e2]
  simp only [e1, e2, e3] at h
  rwa [lintegral_sub_left_eq_self K ξ] at h

theorem lintegral_conv_sq_le_mul {K G : E → ℝ≥0∞} (hK : Measurable K) (hG : Measurable G) :
    ∫⁻ ξ, (∫⁻ η, K (ξ - η) * G η) ^ 2 ≤ (∫⁻ ζ, K ζ) ^ 2 * ∫⁻ η, G η ^ 2 := by
  have hm : Measurable (Function.uncurry fun ξ η : E ↦ K (ξ - η) * G η ^ 2) :=
    (hK.comp (measurable_fst.sub measurable_snd)).mul ((hG.pow_const 2).comp measurable_snd)
  calc ∫⁻ ξ, (∫⁻ η, K (ξ - η) * G η) ^ 2
      ≤ ∫⁻ ξ, (∫⁻ ζ, K ζ) * ∫⁻ η, K (ξ - η) * G η ^ 2 :=
        lintegral_mono fun ξ ↦ lintegral_conv_sq_le hK hG ξ
    _ = (∫⁻ ζ, K ζ) * ∫⁻ ξ, ∫⁻ η, K (ξ - η) * G η ^ 2 :=
        lintegral_const_mul _ hm.lintegral_prod_right'
    _ = (∫⁻ ζ, K ζ) * ∫⁻ η, ∫⁻ ξ, K (ξ - η) * G η ^ 2 := by
        rw [lintegral_lintegral_swap hm.aemeasurable]
    _ = (∫⁻ ζ, K ζ) * ∫⁻ η, (∫⁻ ζ, K ζ) * G η ^ 2 := by
        congr 1; apply lintegral_congr; intro η
        rw [lintegral_mul_const _ (show Measurable fun ξ : E ↦ K (ξ - η) from
          hK.comp (measurable_id.sub measurable_const)), lintegral_sub_right_eq_self K η]
    _ = _ := by rw [lintegral_const_mul _ (hG.pow_const 2)]; ring

theorem eLpNorm_le_of_le_conv {h g : E → ℂ} {K : E → ℝ≥0∞} (hK : Measurable K)
    (hg : Measurable g) (hh : ∀ ξ, ‖h ξ‖ₑ ≤ ∫⁻ η, K (ξ - η) * ‖g η‖ₑ) :
    eLpNorm h 2 volume ≤ (∫⁻ ζ, K ζ) * eLpNorm g 2 volume := by
  have hsq : eLpNorm h 2 volume ^ 2 ≤ ((∫⁻ ζ, K ζ) * eLpNorm g 2 volume) ^ 2 := by
    rw [L2Kernel.eLpNorm_two_sq, mul_pow, L2Kernel.eLpNorm_two_sq]
    calc ∫⁻ ξ, ‖h ξ‖ₑ ^ 2 ≤ ∫⁻ ξ, (∫⁻ η, K (ξ - η) * ‖g η‖ₑ) ^ 2 :=
          lintegral_mono fun ξ ↦ by gcongr; exact hh ξ
      _ ≤ _ := lintegral_conv_sq_le_mul hK hg.enorm
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hsq

theorem fourier_smulLeftCLM_apply (χ φ : 𝓢(E, ℂ)) (ξ : E) :
    (𝓕 (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) φ) : 𝓢(E, ℂ)) ξ =
      ∫ η, (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) * (𝓕 φ : 𝓢(E, ℂ)) η := by
  have hφ : ∀ x, φ x = ∫ η, (𝐞 (inner ℝ η x) : ℂ) * (𝓕 φ : 𝓢(E, ℂ)) η := by
    intro x
    have h0 : (𝓕⁻ (𝓕 φ : 𝓢(E, ℂ)) : 𝓢(E, ℂ)) = φ := FourierTransform.fourierInv_fourier_eq φ
    have h : (𝓕⁻ (𝓕 φ : 𝓢(E, ℂ)) : 𝓢(E, ℂ)) x = φ x := by rw [h0]
    rw [← h, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
    rfl
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  have hint : Integrable (Function.uncurry fun x η : E ↦
      (𝐞 (-inner ℝ x ξ) : ℂ) * χ x * ((𝐞 (inner ℝ η x) : ℂ) * (𝓕 φ : 𝓢(E, ℂ)) η))
      ((volume : Measure E).prod volume) := by
    have h := (χ.integrable (μ := (volume : Measure E))).mul_prod
      ((𝓕 φ : 𝓢(E, ℂ)).integrable (μ := (volume : Measure E)))
    refine h.norm.mono' ?_ (ae_of_all _ fun p ↦ ?_)
    · exact Continuous.aestronglyMeasurable (by
        have h1 := χ.continuous
        have h2 := (𝓕 φ : 𝓢(E, ℂ)).continuous
        fun_prop)
    · simp only [Function.uncurry, norm_mul, Circle.norm_coe, one_mul]
      exact le_rfl
  calc ∫ x, 𝐞 (-inner ℝ x ξ) • (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) φ) x
      = ∫ x, ∫ η, (𝐞 (-inner ℝ x ξ) : ℂ) * χ x *
          ((𝐞 (inner ℝ η x) : ℂ) * (𝓕 φ : 𝓢(E, ℂ)) η) := by
        congr 1; ext x
        rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth, hφ x, Circle.smul_def,
          smul_eq_mul, smul_eq_mul]
        simp_rw [← integral_const_mul]
        congr 1; ext η; ring
    _ = ∫ η, ∫ x, (𝐞 (-inner ℝ x ξ) : ℂ) * χ x *
          ((𝐞 (inner ℝ η x) : ℂ) * (𝓕 φ : 𝓢(E, ℂ)) η) := integral_integral_swap hint
    _ = _ := by
        congr 1; ext η
        rw [← fourier_char_smul χ η ξ, Real.fourier_eq, ← integral_mul_const]
        congr 1; ext x
        rw [Circle.smul_def, smul_eq_mul, real_inner_comm η x]
        ring

theorem eLpNorm_fourier_schwartz (f : 𝓢(E, ℂ)) :
    eLpNorm (𝓕 f : 𝓢(E, ℂ)) 2 volume = eLpNorm f 2 volume := by
  have h : ‖(𝓕 f : 𝓢(E, ℂ)).toLp 2 (volume : Measure E)‖ = ‖f.toLp 2 (volume : Measure E)‖ := by
    rw [← SchwartzMap.toLp_fourier_eq, Lp.norm_fourier_eq]
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp] at h
  exact (ENNReal.toReal_eq_toReal_iff' ((𝓕 f : 𝓢(E, ℂ)).memLp 2 volume).eLpNorm_ne_top
    (f.memLp 2 volume).eLpNorm_ne_top).1 h

theorem fourier_fourierMultiplierCLM_weight_apply (r : ℝ) (φ : 𝓢(E, ℂ)) (ξ : E) :
    (𝓕 (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ) : 𝓢(E, ℂ)) ξ =
      weight r ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ := by
  rw [SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq,
    SchwartzMap.smulLeftCLM_apply_apply (weight_hasTemperateGrowth r), smul_eq_mul]

theorem norm_ofSchwartz_eq (r : ℝ) (φ : 𝓢(E, ℂ)) :
    ‖SobolevSpace.ofSchwartz r φ‖ =
      (eLpNorm (fun ξ ↦ weight r ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ) 2 volume).toReal := by
  rw [SobolevSpace.norm_def, bessel_ofSchwartz, SchwartzMap.norm_toLp,
    ← eLpNorm_fourier_schwartz]
  congr 2
  ext ξ
  exact fourier_fourierMultiplierCLM_weight_apply r φ ξ

theorem eLpNorm_weight_fourier_lt_top (r : ℝ) (φ : 𝓢(E, ℂ)) :
    eLpNorm (fun ξ ↦ weight r ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ) 2 volume < (⊤ : ℝ≥0∞) := by
  have h : (fun ξ ↦ weight r ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ) =
      ⇑(𝓕 (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ) : 𝓢(E, ℂ)) := by
    ext ξ; exact (fourier_fourierMultiplierCLM_weight_apply r φ ξ).symm
  rw [h]
  exact ((𝓕 (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ) : 𝓢(E, ℂ)).memLp 2 volume).eLpNorm_lt_top

theorem hasFDerivAt_one_add_norm_sq_rpow (r : ℝ) (ζ : E) :
    HasFDerivAt (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (r / 2))
      ((r / 2 * (1 + ‖ζ‖ ^ 2) ^ (r / 2 - 1)) • (2 • innerSL ℝ ζ)) ζ := by
  have h1 : HasFDerivAt (fun x : E ↦ 1 + ‖x‖ ^ 2) (2 • innerSL ℝ ζ) ζ := by
    have := (hasFDerivAt_id ζ).norm_sq
    simpa using this.const_add 1
  exact h1.rpow_const (Or.inl (by positivity))

theorem norm_fderiv_weight_le (r : ℝ) (ζ : E) :
    ‖(r / 2 * (1 + ‖ζ‖ ^ 2) ^ (r / 2 - 1)) • (2 • innerSL ℝ ζ)‖ ≤
      |r| * (1 + ‖ζ‖ ^ 2) ^ ((r - 1) / 2) := by
  have hp : (0 : ℝ) < 1 + ‖ζ‖ ^ 2 := by positivity
  have h2 : ‖2 • innerSL ℝ ζ‖ ≤ 2 * ‖ζ‖ := by
    refine norm_nsmul_le.trans ?_
    rw [innerSL_apply_norm]; norm_num
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hp _), abs_div,
    abs_two]
  have hζ : ‖ζ‖ ≤ (1 + ‖ζ‖ ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply Real.le_sqrt_of_sq_le
    linarith
  have e : (1 + ‖ζ‖ ^ 2) ^ (r / 2 - 1) * (1 + ‖ζ‖ ^ 2) ^ (1 / 2 : ℝ) =
      (1 + ‖ζ‖ ^ 2) ^ ((r - 1) / 2) := by
    rw [← Real.rpow_add hp]; congr 1; ring
  calc |r| / 2 * (1 + ‖ζ‖ ^ 2) ^ (r / 2 - 1) * ‖2 • innerSL ℝ ζ‖
      ≤ |r| / 2 * (1 + ‖ζ‖ ^ 2) ^ (r / 2 - 1) * (2 * ‖ζ‖) := by gcongr
    _ = |r| * ((1 + ‖ζ‖ ^ 2) ^ (r / 2 - 1) * ‖ζ‖) := by ring
    _ ≤ |r| * ((1 + ‖ζ‖ ^ 2) ^ (r / 2 - 1) * (1 + ‖ζ‖ ^ 2) ^ (1 / 2 : ℝ)) := by gcongr
    _ = _ := by rw [e]

theorem abs_weight_sub_le (r : ℝ) (ξ η : E) :
    |(1 + ‖ξ‖ ^ 2) ^ (r / 2) - (1 + ‖η‖ ^ 2) ^ (r / 2)| ≤
      |r| * 2 ^ (|r - 1| / 2) * ‖ξ - η‖ * (1 + ‖ξ - η‖ ^ 2) ^ (|r - 1| / 2) *
        (1 + ‖η‖ ^ 2) ^ ((r - 1) / 2) := by
  have hbound : ∀ ζ ∈ segment ℝ η ξ,
      ‖(r / 2 * (1 + ‖ζ‖ ^ 2) ^ (r / 2 - 1)) • (2 • innerSL ℝ ζ)‖ ≤
        |r| * (2 ^ (|r - 1| / 2) * (1 + ‖ξ - η‖ ^ 2) ^ (|r - 1| / 2) *
          (1 + ‖η‖ ^ 2) ^ ((r - 1) / 2)) := by
    intro ζ hζ
    refine (norm_fderiv_weight_le r ζ).trans ?_
    gcongr
    have hp := peetre ((r - 1) / 2) ζ η
    rw [abs_div, abs_two] at hp
    refine hp.trans ?_
    gcongr
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hζ
    have : a • η + b • ξ - η = b • (ξ - η) := by
      have ha' : a = 1 - b := by linarith
      rw [ha', sub_smul, one_smul, smul_sub]; abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    have : b ≤ 1 := by linarith
    calc b * ‖ξ - η‖ ≤ 1 * ‖ξ - η‖ := by gcongr
      _ = ‖ξ - η‖ := one_mul _
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (r / 2))
    (fun ζ _ ↦ (hasFDerivAt_one_add_norm_sq_rpow r ζ).hasFDerivWithinAt) hbound
    (convex_segment η ξ) (left_mem_segment ℝ η ξ) (right_mem_segment ℝ η ξ)
  rw [Real.norm_eq_abs] at h
  calc _ ≤ _ := h
    _ = _ := by ring

def wK (c : ℝ) (ψ : 𝓢(E, ℂ)) (ζ : E) : ℝ≥0∞ := ENNReal.ofReal ((1 + ‖ζ‖ ^ 2) ^ c * ‖ψ ζ‖)

theorem continuous_one_add_norm_sq_rpow (c : ℝ) : Continuous fun ζ : E ↦ (1 + ‖ζ‖ ^ 2) ^ c :=
  (continuous_const.add (continuous_norm.pow 2)).rpow_const
    fun ζ ↦ Or.inl (by positivity : (0 : ℝ) < 1 + ‖ζ‖ ^ 2).ne'

theorem measurable_wK (c : ℝ) (ψ : 𝓢(E, ℂ)) : Measurable (wK c ψ) :=
  ENNReal.measurable_ofReal.comp
    ((continuous_one_add_norm_sq_rpow c).mul ψ.continuous.norm).measurable

theorem integrable_wK (c : ℝ) (ψ : 𝓢(E, ℂ)) :
    Integrable (fun ζ : E ↦ (1 + ‖ζ‖ ^ 2) ^ c * ‖ψ ζ‖) (volume : Measure E) := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  obtain ⟨C, hC⟩ := exists_norm_le_weight ψ (-(n + 1) - 2 * c)
  have hint := (integrable_rpow_neg_one_add_norm_sq (E := E) (μ := (volume : Measure E))
    (r := n + 1) (by linarith)).const_mul C
  refine hint.mono' ((continuous_one_add_norm_sq_rpow c).mul ψ.continuous.norm).aestronglyMeasurable
    (ae_of_all _ fun ζ ↦ ?_)
  have pζ : (0 : ℝ) < 1 + ‖ζ‖ ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (1 + ‖ζ‖ ^ 2) ^ c * ‖ψ ζ‖ ≤ (1 + ‖ζ‖ ^ 2) ^ c * (C * (1 + ‖ζ‖ ^ 2) ^ ((-(n + 1) - 2 * c) / 2)) := by
        gcongr; exact hC ζ
    _ = C * (1 + ‖ζ‖ ^ 2) ^ (-(n + 1) / 2) := by
        rw [mul_left_comm, ← Real.rpow_add pζ]; congr 2; ring

def wInt (c : ℝ) (ψ : 𝓢(E, ℂ)) : ℝ := ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ c * ‖ψ ζ‖

theorem wInt_nonneg (c : ℝ) (ψ : 𝓢(E, ℂ)) : 0 ≤ wInt c ψ :=
  integral_nonneg fun ζ ↦ by positivity

theorem lintegral_wK (c : ℝ) (ψ : 𝓢(E, ℂ)) : ∫⁻ ζ, wK c ψ ζ = ENNReal.ofReal (wInt c ψ) := by
  rw [wInt, ofReal_integral_eq_lintegral_ofReal (integrable_wK c ψ)
    (ae_of_all _ fun ζ ↦ by positivity)]
  rfl

theorem measurable_weight_mul_fourier (r : ℝ) (φ : 𝓢(E, ℂ)) :
    Measurable fun ξ ↦ weight r ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ :=
  ((weight_hasTemperateGrowth (E := E) r).1.continuous.mul (𝓕 φ : 𝓢(E, ℂ)).continuous).measurable

variable (χ : 𝓢(E, ℂ))

theorem enorm_weight_mul_fourier_smulLeft_le (r : ℝ) (φ : 𝓢(E, ℂ)) (ξ : E) :
    ‖weight r ξ * (𝓕 (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) φ) : 𝓢(E, ℂ)) ξ‖ₑ ≤
      ∫⁻ η, ENNReal.ofReal (2 ^ (|r| / 2)) * wK (|r| / 2) (𝓕 χ) (ξ - η) *
        ‖weight r η * (𝓕 φ : 𝓢(E, ℂ)) η‖ₑ := by
  rw [fourier_smulLeftCLM_apply, ← integral_const_mul]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun η ↦ ?_)
  rw [wK, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [norm_mul, norm_mul, norm_mul, norm_weight, norm_weight]
  have hp := peetre (r / 2) ξ η
  rw [abs_div, abs_two] at hp
  calc (1 + ‖ξ‖ ^ 2) ^ (r / 2) * (‖(𝓕 χ : 𝓢(E, ℂ)) (ξ - η)‖ * ‖(𝓕 φ : 𝓢(E, ℂ)) η‖)
      ≤ (2 ^ (|r| / 2) * (1 + ‖ξ - η‖ ^ 2) ^ (|r| / 2) * (1 + ‖η‖ ^ 2) ^ (r / 2)) *
          (‖(𝓕 χ : 𝓢(E, ℂ)) (ξ - η)‖ * ‖(𝓕 φ : 𝓢(E, ℂ)) η‖) := by gcongr
    _ = _ := by ring

theorem norm_ofSchwartz_smulLeft_le (r : ℝ) (φ : 𝓢(E, ℂ)) :
    ‖SobolevSpace.ofSchwartz r (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) φ)‖ ≤
      2 ^ (|r| / 2) * wInt (|r| / 2) (𝓕 χ) * ‖SobolevSpace.ofSchwartz r φ‖ := by
  have h := eLpNorm_le_of_le_conv (((measurable_wK (|r| / 2) (𝓕 χ)).const_mul _))
    (measurable_weight_mul_fourier r φ) (enorm_weight_mul_fourier_smulLeft_le χ r φ)
  rw [lintegral_const_mul _ (measurable_wK _ _), lintegral_wK,
    ← ENNReal.ofReal_mul (by positivity)] at h
  rw [norm_ofSchwartz_eq, norm_ofSchwartz_eq]
  have hfin := eLpNorm_weight_fourier_lt_top r φ
  calc _ ≤ (ENNReal.ofReal (2 ^ (|r| / 2) * wInt (|r| / 2) (𝓕 χ)) *
        eLpNorm (fun ξ ↦ weight r ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) h
    _ = _ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (by positivity) (wInt_nonneg _ _))]

def commRem (r : ℝ) (φ : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) φ -
    SchwartzMap.fourierMultiplierCLM ℂ (weight (-r))
      (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ))

theorem weight_mul_fourier_commRem (r : ℝ) (φ : 𝓢(E, ℂ)) (ξ : E) :
    weight r ξ * (𝓕 (commRem χ r φ) : 𝓢(E, ℂ)) ξ =
      ∫ η, (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) * ((weight r ξ - weight r η) * (𝓕 φ : 𝓢(E, ℂ)) η) := by
  have hw : weight r ξ * weight (-r) ξ = 1 := by
    rw [weight_mul_weight, add_neg_cancel]; simp [weight]
  have hi1 : Integrable (fun η ↦ (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) * (𝓕 φ : 𝓢(E, ℂ)) η) volume := by
    refine ((𝓕 φ : 𝓢(E, ℂ)).integrable (μ := (volume : Measure E))).bdd_mul
      (c := SchwartzMap.seminorm ℝ 0 0 (𝓕 χ : 𝓢(E, ℂ))) ?_ ?_
    · exact ((𝓕 χ : 𝓢(E, ℂ)).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · exact ae_of_all _ fun η ↦ SchwartzMap.norm_le_seminorm ℝ _ _
  have hi2 : Integrable (fun η ↦ (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) *
      (𝓕 (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ) : 𝓢(E, ℂ)) η) volume := by
    refine ((𝓕 (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ) : 𝓢(E, ℂ)).integrable
      (μ := (volume : Measure E))).bdd_mul
      (c := SchwartzMap.seminorm ℝ 0 0 (𝓕 χ : 𝓢(E, ℂ))) ?_ ?_
    · exact ((𝓕 χ : 𝓢(E, ℂ)).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · exact ae_of_all _ fun η ↦ SchwartzMap.norm_le_seminorm ℝ _ _
  have e : (𝓕 (commRem χ r φ) : 𝓢(E, ℂ)) = 𝓕 (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) φ) -
      𝓕 (SchwartzMap.fourierMultiplierCLM ℂ (weight (-r))
        (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ))) := by
    simp only [commRem, sub_eq_add_neg, FourierTransform.fourier_add, FourierTransform.fourier_neg]
  rw [e, sub_apply, fourier_fourierMultiplierCLM_weight_apply, fourier_smulLeftCLM_apply,
    fourier_smulLeftCLM_apply]
  rw [mul_sub, ← mul_assoc, hw, one_mul, ← integral_const_mul, ← integral_sub (hi1.const_mul _) hi2]
  congr 1; ext η
  rw [fourier_fourierMultiplierCLM_weight_apply]
  ring

theorem norm_weight_sub_weight (r : ℝ) (ξ η : E) :
    ‖weight r ξ - weight r η‖ = |(1 + ‖ξ‖ ^ 2) ^ (r / 2) - (1 + ‖η‖ ^ 2) ^ (r / 2)| := by
  unfold weight
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

def commConst (r a : ℝ) : ℝ := |r| * 2 ^ (|r - 1| / 2) * 2 ^ (|a| / 2)

theorem commConst_nonneg (r a : ℝ) : 0 ≤ commConst r a := by unfold commConst; positivity

theorem enorm_weight_mul_fourier_commRem_le (r a : ℝ) (φ : 𝓢(E, ℂ)) (ξ : E) :
    ‖weight (r + a) ξ * (𝓕 (commRem χ r φ) : 𝓢(E, ℂ)) ξ‖ₑ ≤
      ∫⁻ η, ENNReal.ofReal (commConst r a) * wK ((|a| + |r - 1| + 1) / 2) (𝓕 χ) (ξ - η) *
        ‖weight (r + a - 1) η * (𝓕 φ : 𝓢(E, ℂ)) η‖ₑ := by
  rw [show r + a = a + r by ring, ← weight_mul_weight a r, mul_assoc, weight_mul_fourier_commRem,
    ← integral_const_mul]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun η ↦ ?_)
  rw [wK, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (commConst_nonneg r a),
    ← ENNReal.ofReal_mul (by have := commConst_nonneg r a; positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_weight, norm_weight,
    norm_weight_sub_weight]
  set X : ℝ := 1 + ‖ξ - η‖ ^ 2
  set Y : ℝ := 1 + ‖η‖ ^ 2
  have hX : 0 < X := by positivity
  have hY : 0 < Y := by positivity
  have hpa := peetre (a / 2) ξ η
  rw [abs_div, abs_two] at hpa
  have hd := abs_weight_sub_le r ξ η
  have hn : ‖ξ - η‖ ≤ X ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]; apply Real.le_sqrt_of_sq_le; simp only [X]; linarith
  have eX : X ^ (|a| / 2) * X ^ (|r - 1| / 2) * X ^ (1 / 2 : ℝ) = X ^ ((|a| + |r - 1| + 1) / 2) := by
    rw [← Real.rpow_add hX, ← Real.rpow_add hX]; congr 1; ring
  have eY : Y ^ (a / 2) * Y ^ ((r - 1) / 2) = Y ^ ((a + r - 1) / 2) := by
    rw [← Real.rpow_add hY]; congr 1; ring
  set A := ‖(𝓕 χ : 𝓢(E, ℂ)) (ξ - η)‖
  set Φ := ‖(𝓕 φ : 𝓢(E, ℂ)) η‖
  have hA : 0 ≤ A := norm_nonneg _
  have hΦ : 0 ≤ Φ := norm_nonneg _
  calc (1 + ‖ξ‖ ^ 2) ^ (a / 2) * (A * (|(1 + ‖ξ‖ ^ 2) ^ (r / 2) - Y ^ (r / 2)| * Φ))
      ≤ (2 ^ (|a| / 2) * X ^ (|a| / 2) * Y ^ (a / 2)) *
          (A * ((|r| * 2 ^ (|r - 1| / 2) * ‖ξ - η‖ * X ^ (|r - 1| / 2) * Y ^ ((r - 1) / 2)) * Φ)) := by
        gcongr
    _ ≤ (2 ^ (|a| / 2) * X ^ (|a| / 2) * Y ^ (a / 2)) *
          (A * ((|r| * 2 ^ (|r - 1| / 2) * X ^ (1 / 2 : ℝ) * X ^ (|r - 1| / 2) *
            Y ^ ((r - 1) / 2)) * Φ)) := by gcongr
    _ = commConst r a * (X ^ (|a| / 2) * X ^ (|r - 1| / 2) * X ^ (1 / 2 : ℝ)) * A *
          ((Y ^ (a / 2) * Y ^ ((r - 1) / 2)) * Φ) := by unfold commConst; ring
    _ = _ := by rw [eX, eY]; ring

theorem norm_ofSchwartz_commRem_le (r a : ℝ) (φ : 𝓢(E, ℂ)) :
    ‖SobolevSpace.ofSchwartz (r + a) (commRem χ r φ)‖ ≤
      commConst r a * wInt ((|a| + |r - 1| + 1) / 2) (𝓕 χ) *
        ‖SobolevSpace.ofSchwartz (r + a - 1) φ‖ := by
  have h := eLpNorm_le_of_le_conv (((measurable_wK _ (𝓕 χ)).const_mul _))
    (measurable_weight_mul_fourier (r + a - 1) φ) (enorm_weight_mul_fourier_commRem_le χ r a φ)
  rw [lintegral_const_mul _ (measurable_wK _ _), lintegral_wK,
    ← ENNReal.ofReal_mul (commConst_nonneg r a)] at h
  rw [norm_ofSchwartz_eq, norm_ofSchwartz_eq]
  have hfin := eLpNorm_weight_fourier_lt_top (r + a - 1) φ
  calc _ ≤ (ENNReal.ofReal (commConst r a * wInt ((|a| + |r - 1| + 1) / 2) (𝓕 χ)) *
        eLpNorm (fun ξ ↦ weight (r + a - 1) ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) h
    _ = _ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
          (mul_nonneg (commConst_nonneg r a) (wInt_nonneg _ _))]

open Classical in

def sob (s : ℝ) (u : 𝓢'(E, ℂ)) : ℝ≥0∞ :=
  if h : MemSobolev s 2 u then ‖(SobolevSpace.mk u h : SobolevSpace E ℂ s)‖ₑ else ⊤

theorem sob_of_mem {s : ℝ} {u : 𝓢'(E, ℂ)} (h : MemSobolev s 2 u) :
    sob s u = ‖(SobolevSpace.mk u h : SobolevSpace E ℂ s)‖ₑ := by rw [sob, dif_pos h]

theorem sob_of_not_mem {s : ℝ} {u : 𝓢'(E, ℂ)} (h : ¬ MemSobolev s 2 u) : sob s u = ⊤ := by rw [sob, dif_neg h]

theorem mk_toDistribution {s : ℝ} (v : SobolevSpace E ℂ s) (h) :
    SobolevSpace.mk (SobolevSpace.toDistribution v) h = v :=
  SobolevSpace.toDistribution_injective (by simp)

theorem sob_toDistribution {s : ℝ} (v : SobolevSpace E ℂ s) :
    sob s (SobolevSpace.toDistribution v) = ‖v‖ₑ := by
  rw [sob_of_mem (SobolevSpace.memSobolev_toDistribution v), mk_toDistribution]

theorem sob_congr {s t : ℝ} (h : s = t) (u : 𝓢'(E, ℂ)) : sob s u = sob t u := by subst h; rfl

theorem sob_lt_top_iff {s : ℝ} {u : 𝓢'(E, ℂ)} : sob s u < ⊤ ↔ MemSobolev s 2 u := by
  constructor
  · intro h; by_contra hc; rw [sob_of_not_mem hc] at h; exact lt_irrefl _ h
  · intro h; rw [sob_of_mem h]; exact enorm_lt_top

theorem sob_ofSchwartz {s : ℝ} (φ : 𝓢(E, ℂ)) :
    sob s (φ : 𝓢'(E, ℂ)) = ‖SobolevSpace.ofSchwartz s φ‖ₑ := by
  rw [← sob_toDistribution, SobolevSpace.toDistribution_ofSchwartz]

theorem sob_zero {s : ℝ} : sob s (0 : 𝓢'(E, ℂ)) = 0 := by
  rw [← SobolevSpace.toDistribution_zero (s := s), sob_toDistribution, enorm_zero]

theorem sob_add_le {s : ℝ} (u v : 𝓢'(E, ℂ)) : sob s (u + v) ≤ sob s u + sob s v := by
  by_cases hu : MemSobolev s 2 u
  · by_cases hv : MemSobolev s 2 v
    · obtain ⟨u', rfl⟩ := (SobolevSpace.exists_toDistribution_eq_iff (s := s) u).2 hu
      obtain ⟨v', rfl⟩ := (SobolevSpace.exists_toDistribution_eq_iff (s := s) v).2 hv
      rw [← SobolevSpace.toDistribution_add, sob_toDistribution, sob_toDistribution,
        sob_toDistribution]
      exact enorm_add_le _ _
    · rw [sob_of_not_mem hv, add_top]; exact le_top
  · rw [sob_of_not_mem hu, top_add]; exact le_top

theorem sob_smul_le {s : ℝ} (c : ℂ) (u : 𝓢'(E, ℂ)) : sob s (c • u) ≤ ‖c‖ₑ * sob s u := by
  by_cases hc : c = 0
  · subst hc
    have h0 : (0 : ℂ) • u = 0 := zero_smul ℂ u
    rw [h0, sob_zero]; exact zero_le
  by_cases hu : MemSobolev s 2 u
  · obtain ⟨u', rfl⟩ := (SobolevSpace.exists_toDistribution_eq_iff (s := s) u).2 hu
    rw [← SobolevSpace.toDistribution_smul, sob_toDistribution, sob_toDistribution, enorm_smul]
  · rw [sob_of_not_mem hu, ENNReal.mul_top (by simpa using hc)]; exact le_top

theorem sob_neg {s : ℝ} (u : 𝓢'(E, ℂ)) : sob s (-u) = sob s u := by
  have key : ∀ w : 𝓢'(E, ℂ), sob s (-w) ≤ sob s w := by
    intro w
    calc sob s (-w) = sob s ((-1 : ℂ) • w) := by rw [show ((-1 : ℂ) • w) = -w from neg_one_smul ℂ w]
      _ ≤ ‖(-1 : ℂ)‖ₑ * sob s w := sob_smul_le _ _
      _ = sob s w := by simp
  exact le_antisymm (key u) (by simpa using key (-u))

theorem sob_mono {s t : ℝ} (h : t ≤ s) (u : 𝓢'(E, ℂ)) : sob t u ≤ sob s u := by
  by_cases hu : MemSobolev s 2 u
  · obtain ⟨u', rfl⟩ := (SobolevSpace.exists_toDistribution_eq_iff (s := s) u).2 hu
    calc sob t (SobolevSpace.toDistribution u')
        = sob t (SobolevSpace.toDistribution (SobolevSpace.inclusion h u')) := by
          rw [SobolevSpace.toDistribution_inclusion]
      _ = ‖SobolevSpace.inclusion h u'‖ₑ := sob_toDistribution _
      _ ≤ ‖u'‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (SobolevSpace.norm_inclusion_apply_le h u')
      _ = sob s (SobolevSpace.toDistribution u') := (sob_toDistribution _).symm
  · rw [sob_of_not_mem hu]; exact le_top

theorem ofSchwartz_sub {s : ℝ} (φ ψ : 𝓢(E, ℂ)) :
    SobolevSpace.ofSchwartz s (φ - ψ) = SobolevSpace.ofSchwartz s φ - SobolevSpace.ofSchwartz s ψ := by
  apply SobolevSpace.toDistribution_injective
  simp only [SobolevSpace.toDistribution_ofSchwartz, SobolevSpace.toDistribution_sub, map_sub]

theorem sob_le_of_schwartz (T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) {s t C : ℝ} (hC : 0 ≤ C)
    (h : ∀ φ : 𝓢(E, ℂ), sob t (T φ) ≤ ENNReal.ofReal C * sob s (φ : 𝓢'(E, ℂ))) {u : 𝓢'(E, ℂ)}
    (hu : MemSobolev s 2 u) : sob t (T u) ≤ ENNReal.ofReal C * sob s u := by
  obtain ⟨v, rfl⟩ := (SobolevSpace.exists_toDistribution_eq_iff (s := s) u).2 hu

  have hS : ∀ φ : 𝓢(E, ℂ), ∃ w : SobolevSpace E ℂ t,
      SobolevSpace.toDistribution w = T φ ∧ ‖w‖ ≤ C * ‖SobolevSpace.ofSchwartz s φ‖ := by
    intro φ
    have h1 := h φ
    rw [sob_ofSchwartz] at h1
    have hmem : MemSobolev t 2 (T φ) :=
      sob_lt_top_iff.1 (h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top enorm_lt_top))
    refine ⟨SobolevSpace.mk _ hmem, rfl, ?_⟩
    rw [sob_of_mem hmem, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hC] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  choose S hST hSn using hS
  have hSsub : ∀ φ ψ : 𝓢(E, ℂ), S φ - S ψ = S (φ - ψ) := by
    intro φ ψ
    apply SobolevSpace.toDistribution_injective
    rw [SobolevSpace.toDistribution_sub, hST, hST, hST, map_sub, map_sub]
  obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.1
    (SobolevSpace.denseRange_ofSchwartz (E := E) (F := ℂ) (s := s) v)
  choose φ hφ using hx
  set w : ℕ → SobolevSpace E ℂ t := fun n ↦ S (φ n)
  have hdist : ∀ m n, dist (w m) (w n) ≤ C * dist (x m) (x n) := by
    intro m n
    rw [dist_eq_norm, dist_eq_norm, hSsub, ← hφ m, ← hφ n, ← ofSchwartz_sub]
    exact hSn _
  have hcauchy : CauchySeq w := by
    have hxc := hlim.cauchySeq
    rw [Metric.cauchySeq_iff] at hxc ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hxc (ε / (C + 1)) (by positivity)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    calc dist (w m) (w n) ≤ C * dist (x m) (x n) := hdist m n
      _ ≤ C * (ε / (C + 1)) := by gcongr; exact (hN m hm n hn).le
      _ < ε := by
          rw [mul_div_assoc']; rw [div_lt_iff₀ (by positivity)]; nlinarith
  obtain ⟨w₀, hw₀⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hT : SobolevSpace.toDistribution w₀ = T (SobolevSpace.toDistribution v) := by
    have h1 := ((SobolevSpace.toDistributionCLM E ℂ t).continuous.tendsto w₀).comp hw₀
    simp only [Function.comp_def, SobolevSpace.toDistributionCLM_apply] at h1
    have h2 : Filter.Tendsto (fun n ↦ SobolevSpace.toDistribution (w n)) Filter.atTop
        (nhds (T (SobolevSpace.toDistribution v))) := by
      have h3 := (T.continuous.tendsto _).comp
        (((SobolevSpace.toDistributionCLM E ℂ s).continuous.tendsto v).comp hlim)
      simp only [Function.comp_def, SobolevSpace.toDistributionCLM_apply] at h3
      refine h3.congr fun n ↦ ?_
      simp only [w, hST, ← hφ n, SobolevSpace.toDistribution_ofSchwartz]
    exact tendsto_nhds_unique h1 h2
  rw [← hT, sob_toDistribution, sob_toDistribution, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul hC]
  apply ENNReal.ofReal_le_ofReal
  have hn : Filter.Tendsto (fun n ↦ ‖w n‖) Filter.atTop (nhds ‖w₀‖) := hw₀.norm
  have hm : Filter.Tendsto (fun n ↦ C * ‖x n‖) Filter.atTop (nhds (C * ‖v‖)) :=
    hlim.norm.const_mul C
  refine le_of_tendsto_of_tendsto hn hm (Filter.Eventually.of_forall fun n ↦ ?_)
  simp only [w]
  rw [← hφ n]
  exact hSn _

theorem smulLeftCLM_coe (χ : 𝓢(E, ℂ)) (φ : 𝓢(E, ℂ)) :
    smulLeftCLM ℂ (χ : E → ℂ) (φ : 𝓢'(E, ℂ)) =
      ((SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) φ : 𝓢(E, ℂ)) : 𝓢'(E, ℂ)) := by
  ext ψ
  rw [smulLeftCLM_apply_apply, SchwartzMap.coe_apply, SchwartzMap.coe_apply]
  congr 1; ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, smul_eq_mul]
  ring

def mulConst (r : ℝ) (χ : 𝓢(E, ℂ)) : ℝ := 2 ^ (|r| / 2) * wInt (|r| / 2) (𝓕 χ)

theorem mulConst_nonneg (r : ℝ) (χ : 𝓢(E, ℂ)) : 0 ≤ mulConst r χ :=
  mul_nonneg (by positivity) (wInt_nonneg _ _)

theorem sob_smulLeft_le (χ : 𝓢(E, ℂ)) (r : ℝ) {u : 𝓢'(E, ℂ)} (hu : MemSobolev r 2 u) :
    sob r (smulLeftCLM ℂ (χ : E → ℂ) u) ≤ ENNReal.ofReal (mulConst r χ) * sob r u := by
  refine sob_le_of_schwartz _ (mulConst_nonneg r χ) (fun φ ↦ ?_) hu
  rw [smulLeftCLM_coe, sob_ofSchwartz, sob_ofSchwartz, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (mulConst_nonneg r χ)]
  exact ENNReal.ofReal_le_ofReal (norm_ofSchwartz_smulLeft_le χ r φ)

theorem memSobolev_smulLeft (χ : 𝓢(E, ℂ)) {r : ℝ} {u : 𝓢'(E, ℂ)} (hu : MemSobolev r 2 u) :
    MemSobolev r 2 (smulLeftCLM ℂ (χ : E → ℂ) u) :=
  sob_lt_top_iff.1 ((sob_smulLeft_le χ r hu).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (sob_lt_top_iff.2 hu)))

def mulPrin (χ : 𝓢(E, ℂ)) (r : ℝ) : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) :=
  fourierMultiplierCLM ℂ (weight (-r)) ∘L smulLeftCLM ℂ (χ : E → ℂ) ∘L
    fourierMultiplierCLM ℂ (weight r)

def mulRem (χ : 𝓢(E, ℂ)) (r : ℝ) : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) :=
  smulLeftCLM ℂ (χ : E → ℂ) - mulPrin χ r

theorem smulLeftCLM_eq_mulPrin_add_mulRem (χ : 𝓢(E, ℂ)) (r : ℝ) (u : 𝓢'(E, ℂ)) :
    smulLeftCLM ℂ (χ : E → ℂ) u = mulPrin χ r u + mulRem χ r u := by
  simp [mulRem]

theorem mulPrin_coe (χ : 𝓢(E, ℂ)) (r : ℝ) (φ : 𝓢(E, ℂ)) :
    mulPrin χ r (φ : 𝓢'(E, ℂ)) =
      ((SchwartzMap.fourierMultiplierCLM ℂ (weight (-r)) (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ)
        (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ)) : 𝓢(E, ℂ)) : 𝓢'(E, ℂ)) := by
  simp only [mulPrin, ContinuousLinearMap.comp_apply]
  rw [fourierMultiplierCLM_toTemperedDistributionCLM_eq (weight_hasTemperateGrowth r),
    smulLeftCLM_coe, fourierMultiplierCLM_toTemperedDistributionCLM_eq (weight_hasTemperateGrowth _)]

theorem mulRem_coe (χ : 𝓢(E, ℂ)) (r : ℝ) (φ : 𝓢(E, ℂ)) :
    mulRem χ r (φ : 𝓢'(E, ℂ)) = ((commRem χ r φ : 𝓢(E, ℂ)) : 𝓢'(E, ℂ)) := by
  rw [mulRem, sub_apply, mulPrin_coe, smulLeftCLM_coe, commRem, map_sub]

theorem sob_mulPrin_le (χ : 𝓢(E, ℂ)) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, ‖χ x‖ ≤ M) (r : ℝ)
    {u : 𝓢'(E, ℂ)} (hu : MemSobolev r 2 u) :
    sob r (mulPrin χ r u) ≤ ENNReal.ofReal M * sob r u := by
  refine sob_le_of_schwartz _ hM0 (fun φ ↦ ?_) hu
  rw [mulPrin_coe, sob_ofSchwartz, sob_ofSchwartz, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul hM0]
  apply ENNReal.ofReal_le_ofReal
  set g : 𝓢(E, ℂ) := SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ)
    (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ)
  have e1 : (fun ξ ↦ weight r ξ * (𝓕 (SchwartzMap.fourierMultiplierCLM ℂ (weight (-r)) g) :
      𝓢(E, ℂ)) ξ) = ⇑(𝓕 g : 𝓢(E, ℂ)) := by
    ext ξ
    rw [fourier_fourierMultiplierCLM_weight_apply, ← mul_assoc, weight_mul_weight, add_neg_cancel]
    simp [weight]
  have e2 : (fun ξ ↦ weight r ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ) =
      ⇑(𝓕 (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ) : 𝓢(E, ℂ)) := by
    ext ξ; rw [fourier_fourierMultiplierCLM_weight_apply]
  rw [norm_ofSchwartz_eq, norm_ofSchwartz_eq, e1, e2, eLpNorm_fourier_schwartz,
    eLpNorm_fourier_schwartz]
  have hle : eLpNorm g 2 volume ≤
      ENNReal.ofReal M * eLpNorm (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ) 2 volume := by
    have := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (p := 2) (μ := (volume : Measure E))
      (f := g) (g := SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ) (c := M.toNNReal)
      (ae_of_all _ fun x ↦ ?_)
    · rw [ENNReal.ofReal]; exact this
    · rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm, Real.coe_toNNReal _ hM0]
      simp only [g, SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth, smul_eq_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
  have hfin := ((SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ).memLp 2 volume).eLpNorm_lt_top
  calc (eLpNorm g 2 volume).toReal ≤
      (ENNReal.ofReal M * eLpNorm (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) hle
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM0]

theorem sob_mulRem_le (χ : 𝓢(E, ℂ)) (r a : ℝ) {u : 𝓢'(E, ℂ)} (hu : MemSobolev (r + a - 1) 2 u) :
    sob (r + a) (mulRem χ r u) ≤
      ENNReal.ofReal (commConst r a * wInt ((|a| + |r - 1| + 1) / 2) (𝓕 χ)) *
        sob (r + a - 1) u := by
  have hC := mul_nonneg (commConst_nonneg r a) (wInt_nonneg ((|a| + |r - 1| + 1) / 2) (𝓕 χ))
  refine sob_le_of_schwartz _ hC (fun φ ↦ ?_) hu
  rw [mulRem_coe, sob_ofSchwartz, sob_ofSchwartz, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal (norm_ofSchwartz_commRem_le χ r a φ)

theorem sob_fourierMultiplier_le {m : E → ℂ} (hm : m.HasTemperateGrowth) {C s t : ℝ}
    (hC : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) {u : 𝓢'(E, ℂ)} (hu : MemSobolev s 2 u) :
    sob t (fourierMultiplierCLM ℂ m u) ≤ ENNReal.ofReal C * sob s u := by
  obtain ⟨v, rfl⟩ := (SobolevSpace.exists_toDistribution_eq_iff (s := s) u).2 hu
  rw [← SobolevSpace.toDistribution_multiplier hm hC, sob_toDistribution, sob_toDistribution,
    ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (bound_nonneg hC)]
  exact ENNReal.ofReal_le_ofReal (SobolevSpace.norm_multiplier_apply_le hm hC v)

theorem memSobolev_of_sob_le {s t : ℝ} {u v : 𝓢'(E, ℂ)} {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (h : sob t v ≤ C * sob s u) (hu : MemSobolev s 2 u) : MemSobolev t 2 v :=
  sob_lt_top_iff.1 (h.trans_lt (ENNReal.mul_lt_top hC.lt_top (sob_lt_top_iff.2 hu)))

theorem sob_lineDeriv_le (v : E) {s : ℝ} {u : 𝓢'(E, ℂ)} (hu : MemSobolev s 2 u) :
    sob (s - 1) (LineDeriv.lineDerivOp v u) ≤ ENNReal.ofReal (2 * Real.pi * ‖v‖) * sob s u := by
  obtain ⟨w, rfl⟩ := (SobolevSpace.exists_toDistribution_eq_iff (s := s) u).2 hu
  rw [← SobolevSpace.toDistribution_lineDerivCLM, sob_toDistribution, sob_toDistribution,
    ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (SobolevSpace.norm_lineDerivCLM_apply_le v w)

end

end GroundTheory.Automorphic.Sobolev
