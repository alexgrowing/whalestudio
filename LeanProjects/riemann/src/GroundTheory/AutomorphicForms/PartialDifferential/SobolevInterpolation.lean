import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.SobolevFriedrichs

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem one_add_norm_sq_le (ξ η : E) :
    1 + ‖ξ‖ ^ 2 ≤ 2 * (1 + ‖ξ - η‖ ^ 2) * (1 + ‖η‖ ^ 2) := by
  have h : ‖ξ‖ ≤ ‖ξ - η‖ + ‖η‖ := by
    simpa using norm_add_le (ξ - η) η
  have h2 : ‖ξ‖ ^ 2 ≤ 2 * ‖ξ - η‖ ^ 2 + 2 * ‖η‖ ^ 2 := by
    nlinarith [norm_nonneg ξ, norm_nonneg (ξ - η), norm_nonneg η, sq_nonneg (‖ξ - η‖ - ‖η‖)]
  nlinarith [sq_nonneg ‖ξ - η‖, sq_nonneg ‖η‖, mul_nonneg (sq_nonneg ‖ξ - η‖) (sq_nonneg ‖η‖)]

theorem peetre (r : ℝ) (ξ η : E) :
    (1 + ‖ξ‖ ^ 2) ^ r ≤ 2 ^ |r| * (1 + ‖ξ - η‖ ^ 2) ^ |r| * (1 + ‖η‖ ^ 2) ^ r := by
  have pξ : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  have pη : (0 : ℝ) < 1 + ‖η‖ ^ 2 := by positivity
  have pζ : (0 : ℝ) < 1 + ‖ξ - η‖ ^ 2 := by positivity
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr, ← Real.mul_rpow (by norm_num) pζ.le, ← Real.mul_rpow (by positivity) pη.le]
    exact Real.rpow_le_rpow pξ.le (one_add_norm_sq_le ξ η) hr
  · rw [abs_of_nonpos hr]
    have key : (1 + ‖η‖ ^ 2) ^ (-r) ≤ 2 ^ (-r) * (1 + ‖ξ - η‖ ^ 2) ^ (-r) * (1 + ‖ξ‖ ^ 2) ^ (-r) := by
      rw [← Real.mul_rpow (by norm_num) pζ.le, ← Real.mul_rpow (by positivity) pξ.le]
      apply Real.rpow_le_rpow pη.le _ (by linarith)
      have := one_add_norm_sq_le η ξ
      rwa [norm_sub_rev] at this
    rw [Real.rpow_neg pη.le, Real.rpow_neg pξ.le] at key
    have a := Real.rpow_pos_of_pos pξ r
    have b := Real.rpow_pos_of_pos pη r
    have c : 0 < 2 ^ (-r) * (1 + ‖ξ - η‖ ^ 2) ^ (-r) := by positivity
    rw [le_mul_inv_iff₀ a, inv_mul_le_iff₀ b] at key
    calc (1 + ‖ξ‖ ^ 2) ^ r = (1 + ‖ξ‖ ^ 2) ^ r * 1 := (mul_one _).symm
      _ ≤ _ := by nlinarith

theorem fourierFun_inclusion {s t : ℝ} (h : t ≤ s) (v : SobolevSpace E F s) :
    fourierFun (SobolevSpace.inclusion h v) =ᵐ[volume] fourierFun v := by
  have := (fourierFun_multiplier (m := fun _ ↦ (1 : ℂ)) (Function.HasTemperateGrowth.const 1)
    (SobolevSpace.one_bound h) v).1
  filter_upwards [this] with ξ hξ
  rw [one_smul] at hξ
  exact hξ

theorem norm_inclusion_sq {s t : ℝ} (h : t ≤ s) (v : SobolevSpace E F s) :
    ‖SobolevSpace.inclusion h v‖ ^ 2 = ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ t * ‖fourierFun v ξ‖ ^ 2 := by
  rw [norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [fourierFun_inclusion h v] with ξ hξ
  rw [hξ]

theorem memLp_rpow_of_integrable {A : E → ℝ} (hA : Integrable A (volume : Measure E))
    (h0 : ∀ ξ, 0 ≤ A ξ) {a : ℝ} (ha : 0 < a) :
    MemLp (fun ξ ↦ A ξ ^ a) (ENNReal.ofReal (1 / a)) (volume : Measure E) := by
  have hm : AEStronglyMeasurable (fun ξ ↦ A ξ ^ a) (volume : Measure E) :=
    (hA.1.aemeasurable.pow_const a).aestronglyMeasurable
  have hq0 : ENNReal.ofReal (1 / a) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  rw [← memLp_norm_rpow_iff hm hq0 ENNReal.ofReal_ne_top,
    ENNReal.div_self hq0 ENNReal.ofReal_ne_top, memLp_one_iff_integrable]
  refine hA.congr (ae_of_all _ fun ξ ↦ ?_)
  simp only
  rw [ENNReal.toReal_ofReal (by positivity), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (h0 ξ) a), ← Real.rpow_mul (h0 ξ), mul_one_div_cancel ha.ne',
    Real.rpow_one]

theorem norm_inclusion_le_interpolation {r t s : ℝ} (hrt : r < t) (hts : t < s)
    (v : SobolevSpace E F s) :
    ‖SobolevSpace.inclusion hts.le v‖ ≤
      ‖v‖ ^ ((t - r) / (s - r)) * ‖SobolevSpace.inclusion (hrt.trans hts).le v‖ ^ ((s - t) / (s - r)) := by
  have hsr : 0 < s - r := by linarith
  set a := (t - r) / (s - r) with ha_def
  set θ := (s - t) / (s - r) with hθ_def
  have ha : 0 < a := div_pos (by linarith) hsr
  have hθ : 0 < θ := div_pos (by linarith) hsr
  have haθ : a + θ = 1 := by rw [ha_def, hθ_def, ← add_div]; field_simp; ring
  have hexp : s * a + r * θ = t := by rw [ha_def, hθ_def]; field_simp; ring
  set A : E → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ s * ‖fourierFun v ξ‖ ^ 2
  set B : E → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ r * ‖fourierFun v ξ‖ ^ 2
  have hA : Integrable A (volume : Measure E) := integrable_weight_mul_norm_sq_fourierFun v
  have hB : Integrable B (volume : Measure E) := by
    have := integrable_weight_mul_norm_sq_fourierFun
      (SobolevSpace.inclusion (hrt.trans hts).le v)
    refine this.congr ?_
    filter_upwards [fourierFun_inclusion (hrt.trans hts).le v] with ξ hξ
    simp only [B, hξ]
  have hA0 : ∀ ξ, 0 ≤ A ξ := fun ξ ↦ by positivity
  have hB0 : ∀ ξ, 0 ≤ B ξ := fun ξ ↦ by positivity
  have hpq : (1 / a).HolderConjugate (1 / θ) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, by simp [haθ]⟩
    rw [lt_div_iff₀ ha, one_mul]; linarith
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (ae_of_all _ fun ξ ↦ Real.rpow_nonneg (hA0 ξ) a) (ae_of_all _ fun ξ ↦ Real.rpow_nonneg (hB0 ξ) θ)
    (memLp_rpow_of_integrable hA hA0 ha) (memLp_rpow_of_integrable hB hB0 hθ)
  have e1 : ∀ ξ, A ξ ^ a * B ξ ^ θ = (1 + ‖ξ‖ ^ 2) ^ t * ‖fourierFun v ξ‖ ^ 2 := by
    intro ξ
    have h0 : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
    simp only [A, B]
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul h0.le, ← Real.rpow_mul h0.le]
    calc (1 + ‖ξ‖ ^ 2) ^ (s * a) * (‖fourierFun v ξ‖ ^ 2) ^ a *
          ((1 + ‖ξ‖ ^ 2) ^ (r * θ) * (‖fourierFun v ξ‖ ^ 2) ^ θ)
        = ((1 + ‖ξ‖ ^ 2) ^ (s * a) * (1 + ‖ξ‖ ^ 2) ^ (r * θ)) *
          ((‖fourierFun v ξ‖ ^ 2) ^ a * (‖fourierFun v ξ‖ ^ 2) ^ θ) := by ring
      _ = _ := by
        rw [← Real.rpow_add h0, hexp, ← Real.rpow_add_of_nonneg (by positivity) ha.le hθ.le, haθ,
          Real.rpow_one]
  have e2 : ∀ ξ, (A ξ ^ a) ^ (1 / a) = A ξ := fun ξ ↦ by
    rw [← Real.rpow_mul (hA0 ξ), mul_one_div_cancel ha.ne', Real.rpow_one]
  have e3 : ∀ ξ, (B ξ ^ θ) ^ (1 / θ) = B ξ := fun ξ ↦ by
    rw [← Real.rpow_mul (hB0 ξ), mul_one_div_cancel hθ.ne', Real.rpow_one]
  simp only [e1, e2, e3, one_div_one_div] at hH
  rw [← norm_inclusion_sq hts.le, ← norm_sq_eq_integral,
    ← norm_inclusion_sq (hrt.trans hts).le] at hH
  have hsq : ∀ (x : ℝ) (c : ℝ), 0 ≤ x → (x ^ 2) ^ c = (x ^ c) ^ 2 := fun x c hx ↦ by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_mul hx, mul_comm]
  rw [hsq _ _ (norm_nonneg _), hsq _ _ (norm_nonneg _), ← mul_pow] at hH
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hH

end

end GroundTheory.Automorphic.Sobolev
