import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsZonalPairing
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.ZonalPairingCalculus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Polynomial MeasureTheory Set

noncomputable section

theorem ZonalKernelPairing.proof : ZonalKernelPairing.Statement := by
  intro F H
  obtain ⟨GF, hGF, hdGF, hGFm, hGFp⟩ := exists_centredPrimitive_poly F
  obtain ⟨GH, hGH, hdGH, hGHm, hGHp⟩ := exists_centredPrimitive_poly H
  obtain ⟨w, hw⟩ := exists_eq_sq_sub_one_mul GH hGHm hGHp
  obtain ⟨ρ, hρ⟩ := exists_polynomial_antiderivative (-((X + C 1) * w))
  obtain ⟨σ, hσ⟩ := exists_polynomial_antiderivative ((C 1 - X) * w)
  set eF := uniformMean F.eval with heF
  set eH := uniformMean H.eval with heH
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
    simp [ae_iff]
  have hinner : ∫ c₁ in (-1 : ℝ)..1, ∫ c₂ in (-1 : ℝ)..1,
        zonalKernel c₁ c₂ * F.eval c₁ * H.eval c₂ =
      ∫ x in (-1 : ℝ)..1,
        (-eH + (1 / 2) * (ρ.eval x - ρ.eval (-1) - σ.eval x + σ.eval 1)) * F.eval x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae] with x hx1 hxI
    rw [uIoc_of_le (by norm_num)] at hxI
    have hx : x ∈ Ioo (-1 : ℝ) 1 := ⟨hxI.1, lt_of_le_of_ne hxI.2 hx1⟩
    have hfun : (fun c₂ => zonalKernel x c₂ * F.eval x * H.eval c₂) =
        fun c₂ => F.eval x * (zonalKernel x c₂ * H.eval c₂) := by
      funext c₂
      ring
    rw [hfun, intervalIntegral.integral_const_mul,
      integral_zonalKernel_mul_eval H w ρ σ eH (by rw [← hw, hdGH]) hρ hσ hx]
    ring
  have hrhs : ∫ c in (-1 : ℝ)..1, centredPrimitive F c * centredPrimitive H c / (1 - c ^ 2) =
      -∫ c in (-1 : ℝ)..1, GF.eval c * w.eval c := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae] with x hx1 hxI
    rw [uIoc_of_le (by norm_num)] at hxI
    have hxlt : x < 1 := lt_of_le_of_ne hxI.2 hx1
    have hpos : 0 < 1 - x ^ 2 := by
      nlinarith [mul_pos (sub_pos.2 hxlt) (show 0 < 1 + x by linarith [hxI.1])]
    rw [hGF, hGH, hw]
    simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_C]
    field_simp
    ring
  have hibp : ∫ x in (-1 : ℝ)..1,
        (-eH + (1 / 2) * (ρ.eval x - ρ.eval (-1) - σ.eval x + σ.eval 1)) * F.eval x =
      (-eH + (1 / 2) * (ρ.eval 1 - ρ.eval (-1) - σ.eval 1 + σ.eval 1)) * (GF.eval 1 + eF * (1 + 1)) -
        (-eH + (1 / 2) * (ρ.eval (-1) - ρ.eval (-1) - σ.eval (-1) + σ.eval 1)) *
          (GF.eval (-1) + eF * (1 + -1)) -
        ∫ x in (-1 : ℝ)..1, -w.eval x * (GF.eval x + eF * (1 + x)) := by
    have hu : ∀ x ∈ uIcc (-1 : ℝ) 1, HasDerivAt
        (fun x => -eH + (1 / 2) * (ρ.eval x - ρ.eval (-1) - σ.eval x + σ.eval 1)) (-w.eval x) x := by
      intro x _
      have h := ((((ρ.hasDerivAt x).sub_const (ρ.eval (-1))).sub (σ.hasDerivAt x)).add_const
        (σ.eval 1)).const_mul (1 / 2) |>.const_add (-eH)
      refine h.congr_deriv ?_
      rw [hρ, hσ]
      simp only [eval_neg, eval_mul, eval_add, eval_sub, eval_C, eval_X]
      ring
    have hv : ∀ x ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun x => GF.eval x + eF * (1 + x)) (F.eval x) x := by
      intro x _
      have h := (GF.hasDerivAt x).add (((hasDerivAt_id x).const_add 1).const_mul eF)
      refine h.congr_deriv ?_
      rw [hdGF]
      simp only [eval_sub, eval_C]
      ring
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
      ((w.continuous.neg).intervalIntegrable _ _) (F.continuous.intervalIntegrable _ _)
  have hρint : ∫ x in (-1 : ℝ)..1, -((x + 1) * w.eval x) = ρ.eval 1 - ρ.eval (-1) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => ρ.eval x) ?_ ?_
    · intro x _
      refine (ρ.hasDerivAt x).congr_deriv ?_
      rw [hρ]
      simp
    · exact (((continuous_id.add continuous_const).mul w.continuous).neg).intervalIntegrable _ _
  have hsplit : ∫ x in (-1 : ℝ)..1, -w.eval x * (GF.eval x + eF * (1 + x)) =
      -(∫ x in (-1 : ℝ)..1, GF.eval x * w.eval x) + eF * ∫ x in (-1 : ℝ)..1, -((x + 1) * w.eval x) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg,
      ← intervalIntegral.integral_add]
    · congr 1
      funext x
      ring
    · exact ((GF.continuous.mul w.continuous).neg).intervalIntegrable _ _
    · exact (continuous_const.mul
        ((continuous_id.add continuous_const).mul w.continuous).neg).intervalIntegrable _ _
  rw [hinner, hrhs, hibp, hsplit, hρint, hGFm, hGFp]
  ring

end

end GroundTheory.Heights₂.Heights.FlagBundles
