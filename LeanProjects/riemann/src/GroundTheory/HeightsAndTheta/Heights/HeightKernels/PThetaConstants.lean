import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsTheta
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

namespace KThetaConstants

lemma log_lhs (C₃ ρ d : ℝ) (g : ℕ) (hC₃ : 0 < C₃) (hg : (0 : ℝ) < g) (hρ : 0 < ρ) (hd : 0 < d) :
    Real.log ((C₃ * g) ^ ((g : ℝ) / 2) * d ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g) =
      (g / 2) * Real.log (C₃ * g) + (-(1 / 2)) * Real.log d + g * Real.log (1 + 1 / ρ) := by
  have h1 : 0 < C₃ * g := mul_pos hC₃ hg
  have h2 : 0 < 1 + 1 / ρ := by positivity
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_rpow h1, Real.log_rpow hd, Real.log_pow]

lemma log_rhs (C ρ d : ℝ) (g : ℕ) (hd : 0 < d) :
    Real.log (((2 : ℝ) ^ g * d) ^ (-(1 / 4 : ℝ)) *
        exp (g * Real.log (1 + 1 / ρ) + C * g * Real.log (2 * g))) =
      (-(1 / 4)) * (g * Real.log 2 + Real.log d) +
        (g * Real.log (1 + 1 / ρ) + C * g * Real.log (2 * g)) := by
  have h1 : 0 < (2 : ℝ) ^ g * d := by positivity
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow h1, Real.log_exp,
    Real.log_mul (by positivity) hd.ne', Real.log_pow]

end KThetaConstants

open KThetaConstants in

theorem ThetaConstants.proof : ThetaConstants.Statement := by
  intro C₃ hC₃
  have hK1 : (1 : ℝ) ≤ max C₃ 1 := le_max_right _ _
  have hK0 : (0 : ℝ) < max C₃ 1 := by linarith
  have hlK : 0 ≤ Real.log (max C₃ 1) := Real.log_nonneg hK1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + Real.log (max C₃ 1) / (2 * Real.log 2), by positivity, ?_⟩
  intro g ρ d hg hρ hd hρ2 hdinv
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hg0 : (0 : ℝ) < g := by linarith
  have h2g : (0 : ℝ) < 2 * g := by linarith
  have hl2g : Real.log 2 ≤ Real.log (2 * g) := Real.log_le_log (by norm_num) (by linarith)
  have h1 : -Real.log d ≤ g * Real.log (2 * g) := by
    have hpow : ρ ^ 2 * (2 * (g : ℝ)) ^ (g - 1) ≤ (2 * (g : ℝ)) ^ g := by
      obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := ⟨g - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ' (2 * ((n + 1 : ℕ) : ℝ)) n]
      exact mul_le_mul_of_nonneg_right hρ2 (pow_nonneg h2g.le n)
    have := Real.log_le_log (inv_pos.mpr hd) (hdinv.trans hpow)
    rwa [Real.log_inv, Real.log_pow] at this
  have h2 : Real.log (C₃ * g) ≤ Real.log (max C₃ 1) + Real.log (2 * g) := by
    rw [← Real.log_mul hK0.ne' h2g.ne']
    apply Real.log_le_log (mul_pos hC₃ hg0)
    have : C₃ ≤ max C₃ 1 := le_max_left _ _
    nlinarith [mul_le_mul_of_nonneg_right this hg0.le,
      mul_le_mul_of_nonneg_left (show (g : ℝ) ≤ 2 * g by linarith) hK0.le]
  have h5 : (g : ℝ) / 2 * Real.log (max C₃ 1) ≤
      Real.log (max C₃ 1) / (2 * Real.log 2) * g * Real.log (2 * g) := by
    rw [show Real.log (max C₃ 1) / (2 * Real.log 2) * g * Real.log (2 * g) =
        (g * Real.log (max C₃ 1) * Real.log (2 * g)) / (2 * Real.log 2) by ring,
      le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hl2g (mul_nonneg hg0.le hlK)]
  have ha := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ g / 2 by positivity)
  have hc := mul_le_mul_of_nonneg_left hl2g hg0.le
  rw [← Real.log_le_log_iff (by positivity) (by positivity), log_lhs C₃ ρ d g hC₃ hg0 hρ hd,
    log_rhs _ ρ d g hd]
  nlinarith [h1, ha, hc, h5]

end GroundTheory.Heights₂.Heights
