import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real

theorem AvoidMatrixLemma.proof : AvoidMatrixLemma.Statement := by
  intro a c N x ha hc hN hx
  have hs : 0 < c + 2 * a * N := by positivity
  have ht : 0 < c + N * x := by positivity

  have hlog : log (c + N * x) - log (c + 2 * a * N)
      ≤ (N * (x - 2 * a)) / (c + 2 * a * N) := by
    rw [← Real.log_div ht.ne' hs.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos ht hs)
    have h2 : (c + N * x) / (c + 2 * a * N) - 1 = (N * (x - 2 * a)) / (c + 2 * a * N) := by
      field_simp
      ring
    linarith

  have hbound : a * ((N * (x - 2 * a)) / (c + 2 * a * N)) ≤ x / 2 := by
    rcases le_or_gt x (2 * a) with hxa | hxa
    · have : N * (x - 2 * a) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN.le (by linarith)
      have : (N * (x - 2 * a)) / (c + 2 * a * N) ≤ 0 := div_nonpos_of_nonpos_of_nonneg this hs.le
      nlinarith
    · rw [← mul_div_assoc, div_le_iff₀ hs]
      have hpos : 0 < x - 2 * a := by linarith
      nlinarith [mul_pos hc hpos, mul_pos (mul_pos ha hN) hpos]
  have := mul_le_mul_of_nonneg_left hlog ha.le
  nlinarith

end GroundTheory.Heights₂.Heights.LowerBound
