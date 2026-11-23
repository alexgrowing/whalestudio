import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsIntervalMoments
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsSpherePowerMean
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

instance SphereHeightUniform.isFiniteMeasure_sphereMeasure : IsFiniteMeasure sphereMeasure := by
  unfold sphereMeasure
  refine ⟨?_⟩
  rw [Measure.smul_apply, smul_eq_mul]
  have h0 : (volume : Measure E3).toSphere Set.univ ≠ 0 := by
    rw [Ne, Measure.measure_univ_eq_zero]
    exact Measure.toSphere_ne_zero _
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr h0)) (measure_lt_top _ _)

theorem SphereHeightUniform.proof (hM : IntervalMomentsDetermine.Statement)
    (hP : SpherePowerMean.Statement) : SphereHeightUniform.Statement := by
  intro u hu
  have hc : Continuous fun n : Sphere2 => ⟪u, (n : E3)⟫_ℝ :=
    continuous_const.inner continuous_subtype_val
  have hfin : IsFiniteMeasure ((2⁻¹ : ENNReal) • (volume : Measure ℝ).restrict (Set.Icc (-1) 1)) :=
    ⟨by simp [ENNReal.mul_lt_top]⟩
  refine hM _ _ inferInstance hfin ?_ ?_ ?_
  · rw [Measure.map_apply hc.measurable measurableSet_Icc.compl]
    convert measure_empty (μ := sphereMeasure)
    ext n
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc, Set.mem_empty_iff_false,
      iff_false, not_not]
    have h1 := abs_real_inner_le_norm u (n : E3)
    rw [hu, one_mul, show ‖(n : E3)‖ = 1 from by simp] at h1
    exact abs_le.mp h1
  · simp [Measure.restrict_apply measurableSet_Icc.compl]
  · intro k
    rw [integral_map hc.measurable.aemeasurable (continuous_pow k).aestronglyMeasurable,
      hP u hu k, integral_smul_measure, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num)]
    simp [smul_eq_mul]

end

end GroundTheory.Heights₂.Heights.FlagBundles
