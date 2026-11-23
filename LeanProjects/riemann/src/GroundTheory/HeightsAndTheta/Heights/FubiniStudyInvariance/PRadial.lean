import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FSInv

open MeasureTheory

theorem Radial.proof : Radial.Statement := by
  intro N s hs
  have hc : 0 < s⁻¹ := inv_pos.2 hs
  obtain ⟨hI, hV⟩ := GroundTheory.Heights₂.Heights.integral_complex_norm_pow_div s⁻¹ hc 0 N
  have hpt : ∀ t : ℂ, ‖t‖ ^ (2 * N) * (1 / (1 + ‖t‖ ^ 2 * s) ^ (N + 2)) =
      (s⁻¹) ^ (N + 2) * (‖t‖ ^ (2 * N) / (s⁻¹ + ‖t‖ ^ 2) ^ (N + 2 + 0)) := by
    intro t
    have h1 : 1 + ‖t‖ ^ 2 * s = s * (s⁻¹ + ‖t‖ ^ 2) := by field_simp
    have h2 : 0 < s⁻¹ + ‖t‖ ^ 2 := by positivity
    rw [h1, mul_pow, add_zero, inv_pow]
    field_simp
  have hnn : 0 ≤ᵐ[volume] fun t : ℂ => (s⁻¹) ^ (N + 2) * (‖t‖ ^ (2 * N) / (s⁻¹ + ‖t‖ ^ 2) ^ (N + 2 + 0)) :=
    Filter.Eventually.of_forall fun t => by positivity
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal (hI.const_mul _) hnn, integral_const_mul, hV,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [Nat.factorial_zero, Nat.cast_one, mul_one, add_zero, zero_add, pow_one,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
  have hN : (N.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  rw [div_pow, one_pow, show s ^ (N + 2) = s * s ^ (N + 1) by ring]
  field_simp

end GroundTheory.Heights₂.Heights.FSInv
