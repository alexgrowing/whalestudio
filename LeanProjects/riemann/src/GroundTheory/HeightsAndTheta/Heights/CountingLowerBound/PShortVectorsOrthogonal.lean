import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real

noncomputable section

universe u

theorem ShortVectorsOrthogonal.rpow_neg_half_mul_self {vr : ℝ} (hvr : 0 < vr) :
    vr ^ (-(1 / 2 : ℝ)) * vr ^ (-(1 / 2 : ℝ)) = vr⁻¹ := by
  rw [← Real.rpow_add hvr]
  norm_num [Real.rpow_neg_one]

theorem ShortVectorsOrthogonal.proof : ShortVectorsOrthogonal.Statement := by
  intro L _ len E a vr h v w hv hw
  set r := vr ^ (-(1 / 2 : ℝ)) with hr
  have hvr := h.vr_pos
  have hr_pos : 0 < r := Real.rpow_pos_of_pos hvr _
  have hrr : vr * (r * r) = 1 := by
    rw [hr, ShortVectorsOrthogonal.rpow_neg_half_mul_self hvr, mul_inv_cancel₀ hvr.ne']
  have hv0 := h.len_nonneg v
  have hw0 := h.len_nonneg w
  have hprod : len v * len w < r * r := by
    calc len v * len w ≤ len v * r := mul_le_mul_of_nonneg_left hw.le hv0
      _ < r * r := mul_lt_mul_of_pos_right hv hr_pos
  have hbound : |(E (a v) w : ℝ)| < 1 := by
    calc |(E (a v) w : ℝ)| ≤ len (a v) * len w := h.abs_E_le (a v) w
      _ ≤ (vr * len v) * len w := mul_le_mul_of_nonneg_right (h.len_a_le v) hw0
      _ = vr * (len v * len w) := by ring
      _ < vr * (r * r) := mul_lt_mul_of_pos_left hprod hvr
      _ = 1 := hrr
  have hint : |E (a v) w| < 1 := by exact_mod_cast hbound
  exact Int.abs_lt_one_iff.mp hint

end

end GroundTheory.Heights₂.Heights.LowerBound
