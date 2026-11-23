import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PowerIntegralStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open MeasureTheory Set Real

noncomputable section

theorem PowerIntegral.integral_rpow_mul_exp_neg_mul {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * exp (-(c * u)) = c ^ (-s) * Gamma s := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := s - 1) (b := c) one_pos
    (by linarith) hc
  have e1 : (-(s - 1 + 1) / 1 : ℝ) = -s := by ring
  have e2 : ((s - 1 + 1) / 1 : ℝ) = s := by ring
  rw [e1, e2, one_div_one, mul_one] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  simp only [rpow_one, neg_mul]

theorem PowerIntegral.integrand_split (a s u t : ℝ) :
    u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u)) =
      (u ^ (s - 1) * exp (-(a ^ 2 * u))) * exp (-u * t ^ 2) := by
  rw [mul_assoc, ← exp_add]
  ring_nf

theorem PowerIntegral.proof : PowerIntegral.Statement := by
  intro a s ha hs
  have hs0 : 0 < s := by linarith
  have hΓ : Gamma s ≠ 0 := (Gamma_pos_of_pos hs0).ne'
  have h1 : ∀ t : ℝ, (t ^ 2 + a ^ 2) ^ (-s) =
      (Gamma s)⁻¹ * ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u)) := by
    intro t
    rw [PowerIntegral.integral_rpow_mul_exp_neg_mul (by positivity) hs0,
      mul_comm ((t ^ 2 + a ^ 2) ^ (-s)), ← mul_assoc, inv_mul_cancel₀ hΓ, one_mul]
  have h2 : ∀ u ∈ Ioi (0 : ℝ), ∫ t : ℝ, u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u)) =
      √π * (u ^ (s - 3 / 2) * exp (-(a ^ 2 * u))) := by
    intro u hu
    have hu : 0 < u := hu
    simp_rw [PowerIntegral.integrand_split a s u]
    rw [integral_const_mul, integral_gaussian, sqrt_div pi_pos.le]
    have e : u ^ (s - 3 / 2) = u ^ (s - 1) / √u := by
      rw [sqrt_eq_rpow, ← rpow_sub hu]
      congr 1
      ring
    have hsu : 0 < √u := sqrt_pos.mpr hu
    rw [e]
    field_simp
  have hmeas : Measurable
      (Function.uncurry fun t u : ℝ => u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u))) := by
    unfold Function.uncurry
    fun_prop
  have hint : Integrable
      (Function.uncurry fun t u : ℝ => u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u)))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine (integrable_prod_iff' hmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
      have hu : 0 < u := hu
      simp only [Function.uncurry_apply_pair]
      simp_rw [PowerIntegral.integrand_split a s u]
      exact (integrable_exp_neg_mul_sq hu).const_mul _
    · have hq : (-1 : ℝ) < s - 3 / 2 := by linarith
      have hI := (integrableOn_rpow_mul_exp_neg_mul_rpow hq one_pos (pow_pos ha 2)).const_mul √π
      refine IntegrableOn.congr_fun hI (fun u hu => ?_) measurableSet_Ioi
      have hu : 0 < u := hu
      simp only [Function.uncurry_apply_pair]
      simp only [rpow_one, neg_mul]
      rw [← h2 u hu]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      exact (norm_of_nonneg (mul_nonneg (rpow_nonneg hu.le _) (exp_pos _).le)).symm
  have hpow : (a ^ 2) ^ (-(s - 1 / 2)) = a ^ (1 - 2 * s) := by
    rw [← rpow_natCast, ← rpow_mul ha.le]
    congr 1
    push_cast
    ring
  have hs' : 0 < s - 1 / 2 := by linarith
  calc ∫ t : ℝ, (t ^ 2 + a ^ 2) ^ (-s)
      = ∫ t : ℝ, (Gamma s)⁻¹ *
          ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u)) :=
        integral_congr_ae (Filter.Eventually.of_forall h1)
    _ = (Gamma s)⁻¹ * ∫ u in Ioi (0 : ℝ), ∫ t : ℝ,
          u ^ (s - 1) * exp (-((t ^ 2 + a ^ 2) * u)) := by
        rw [integral_const_mul, integral_integral_swap hint]
    _ = (Gamma s)⁻¹ * ∫ u in Ioi (0 : ℝ), √π * (u ^ (s - 3 / 2) * exp (-(a ^ 2 * u))) := by
        rw [setIntegral_congr_fun measurableSet_Ioi h2]
    _ = (Gamma s)⁻¹ * (√π * ((a ^ 2) ^ (-(s - 1 / 2)) * Gamma (s - 1 / 2))) := by
        rw [integral_const_mul, show s - 3 / 2 = (s - 1 / 2) - 1 by ring,
          PowerIntegral.integral_rpow_mul_exp_neg_mul (pow_pos ha 2) hs']
    _ = √π * Gamma (s - 1 / 2) / Gamma s * a ^ (1 - 2 * s) := by
        rw [hpow]
        field_simp

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
