import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsVolume
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.TheoremB

theorem Gap4Nef.proof : Gap4Nef.Statement := by
  intro d mu τ0 c0 B hc0 hB10 hBc h0 hoth hmu τ
  have hf : (0 : ℝ) ≤ (d.f : ℝ) := Nat.cast_nonneg _
  have hB0 : 0 < B := by linarith
  have hB2 : 0 ≤ B - 2 := by linarith

  have hlhs : 4 * (d.f : ℝ) * ‖mu‖ ≤ 4 * (d.f : ℝ) := by
    have := mul_le_mul_of_nonneg_left hmu (by positivity : (0 : ℝ) ≤ 4 * (d.f : ℝ))
    simpa using this
  by_cases hτ : τ = τ0
  · rw [hτ]

    have hmid : 4 * (d.f : ℝ) ≤ (B - 2) * (5 * (d.f : ℝ) / B) := by
      rw [mul_div_assoc', le_div_iff₀ hB0]
      nlinarith
    calc 4 * (d.f : ℝ) * ‖mu‖ ≤ 4 * (d.f : ℝ) := hlhs
      _ ≤ (B - 2) * (5 * (d.f : ℝ) / B) := hmid
      _ ≤ (B - 2) * gap d τ0 mu := mul_le_mul_of_nonneg_left h0 hB2
  · have hg := hoth τ hτ

    have heq : 8 * (d.f : ℝ) / c0 * (c0 / 2) = 4 * (d.f : ℝ) := by
      field_simp
      ring
    have hmid : 4 * (d.f : ℝ) ≤ (B - 2) * (c0 / 2) := by
      rw [← heq]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc 4 * (d.f : ℝ) * ‖mu‖ ≤ 4 * (d.f : ℝ) := hlhs
      _ ≤ (B - 2) * (c0 / 2) := hmid
      _ ≤ (B - 2) * gap d τ mu := mul_le_mul_of_nonneg_left hg hB2

end GroundTheory.Heights₂.Heights.TheoremB
