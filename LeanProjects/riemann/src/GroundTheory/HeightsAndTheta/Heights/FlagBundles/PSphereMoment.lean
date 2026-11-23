import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

lemma SphereMoment.exists_unit (a : E3) :
    ∃ u : E3, ‖u‖ = 1 ∧ ∀ n : E3, ⟪a, n⟫_ℝ = ‖a‖ * ⟪u, n⟫_ℝ := by
  by_cases h : a = 0
  · refine ⟨EuclideanSpace.single 0 1, by simp, fun n => by simp [h]⟩
  · have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr h
    refine ⟨‖a‖⁻¹ • a, ?_, fun n => ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hna]
    · rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hna, one_mul]

lemma SphereMoment.moment (h0 : SphereHeightUniform.Statement) (a : E3) (k : ℕ) :
    ∫ n, ⟪a, (n : E3)⟫_ℝ ^ k ∂sphereMeasure =
      ‖a‖ ^ k * (2⁻¹ * ((1 - (-1 : ℝ) ^ (k + 1)) / (k + 1))) := by
  obtain ⟨u, hu, ha⟩ := SphereMoment.exists_unit a
  have hc : Continuous fun n : Sphere2 => ⟪u, (n : E3)⟫_ℝ :=
    continuous_const.inner continuous_subtype_val
  calc ∫ n, ⟪a, (n : E3)⟫_ℝ ^ k ∂sphereMeasure
      = ∫ n, ‖a‖ ^ k * ⟪u, (n : E3)⟫_ℝ ^ k ∂sphereMeasure := by
        simp_rw [ha, mul_pow]
    _ = ‖a‖ ^ k * ∫ n, ⟪u, (n : E3)⟫_ℝ ^ k ∂sphereMeasure := integral_const_mul _ _
    _ = ‖a‖ ^ k * ∫ t, t ^ k ∂(sphereMeasure.map fun n : Sphere2 => ⟪u, (n : E3)⟫_ℝ) := by
        rw [integral_map hc.measurable.aemeasurable
          (continuous_pow k).aestronglyMeasurable]
    _ = ‖a‖ ^ k * (2⁻¹ * ((1 - (-1 : ℝ) ^ (k + 1)) / (k + 1))) := by
        rw [h0 u hu, integral_smul_measure, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by norm_num), integral_pow]
        simp [smul_eq_mul]

theorem SphereMoment.proof (h0 : SphereHeightUniform.Statement) : SphereMoment.Statement := by
  intro a m
  refine ⟨?_, ?_⟩
  · rw [SphereMoment.moment h0, pow_succ, pow_mul]
    have h2 : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    norm_num
    field_simp
  · rw [SphereMoment.moment h0, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul]
    norm_num

end

end GroundTheory.Heights₂.Heights.FlagBundles
