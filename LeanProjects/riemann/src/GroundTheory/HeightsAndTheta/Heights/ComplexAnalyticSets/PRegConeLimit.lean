import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsGreenReg
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFsLogIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Set ConeFsLog

noncomputable section

namespace RegConeLimit

variable {n : ℕ}

theorem abs_fsLogReg_pointOf_le (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n))
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hs : ∑ j, u j * h.pointOf y j ≠ 0) :
    |fsLogReg h u ε (h.pointOf y)| ≤
      |fsLog h u (h.pointOf y)| + Real.log (h.norm u ^ 2 + 1) / 2 := by
  set a := ‖∑ j, u j * h.pointOf y j‖ with ha_def
  set r := ‖y‖ with hr_def
  have ha : 0 < a := norm_pos_iff.mpr hs
  have hCS : a ≤ h.norm u * r := norm_sum_mul_pointOf_le h u y
  have hN : 0 ≤ h.norm u := Real.sqrt_nonneg _
  have hr : 0 < r := by
    by_contra hle
    have h0 : r = 0 := le_antisymm (not_lt.mp hle) (norm_nonneg y)
    rw [h0, mul_zero] at hCS
    linarith
  have hr2 : 0 < r ^ 2 := by positivity
  have hreg : fsLogReg h u ε (h.pointOf y) = Real.log ((a ^ 2 + ε * r ^ 2) / r ^ 2) / 2 := by
    rw [fsLogReg, dualNorm_pointOf]
  have hlog : fsLog h u (h.pointOf y) = Real.log (a / r) := fsLog_pointOf h u y
  have hlow : fsLog h u (h.pointOf y) ≤ fsLogReg h u ε (h.pointOf y) := by
    rw [hreg, hlog]
    have h1 : (a / r) ^ 2 ≤ (a ^ 2 + ε * r ^ 2) / r ^ 2 := by
      rw [div_pow]; gcongr; nlinarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hup : fsLogReg h u ε (h.pointOf y) ≤ Real.log (h.norm u ^ 2 + 1) / 2 := by
    rw [hreg]
    have h1 : (a ^ 2 + ε * r ^ 2) / r ^ 2 ≤ h.norm u ^ 2 + 1 := by
      rw [div_le_iff₀ hr2]
      have : a ^ 2 ≤ (h.norm u * r) ^ 2 := pow_le_pow_left₀ ha.le hCS 2
      nlinarith
    have h2 := Real.log_le_log (by positivity) h1
    linarith
  have hK : 0 ≤ Real.log (h.norm u ^ 2 + 1) / 2 := by
    have : 0 ≤ Real.log (h.norm u ^ 2 + 1) := Real.log_nonneg (by nlinarith)
    linarith
  rw [abs_le]
  constructor
  · have := neg_abs_le (fsLog h u (h.pointOf y))
    linarith
  · have := abs_nonneg (fsLog h u (h.pointOf y))
    linarith

theorem measurable_fsLogReg_pointOf (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) :
    Measurable fun y : EuclideanSpace ℂ (Fin n) => fsLogReg h u ε (h.pointOf y) := by
  have : (fun y : EuclideanSpace ℂ (Fin n) => fsLogReg h u ε (h.pointOf y)) = fun y =>
      Real.log ((‖∑ j, u j * h.pointOf y j‖ ^ 2 + ε * ‖y‖ ^ 2) / ‖y‖ ^ 2) / 2 := by
    funext y; rw [fsLogReg, dualNorm_pointOf]
  rw [this]
  have hp : Continuous fun y : EuclideanSpace ℂ (Fin n) => h.pointOf y := by
    unfold HermNorm.pointOf
    fun_prop
  have hs : Continuous fun y : EuclideanSpace ℂ (Fin n) => ‖∑ j, u j * h.pointOf y j‖ :=
    (continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).comp hp)).norm
  refine (Real.measurable_log.comp (Measurable.div ?_ ?_)).div_const 2
  · exact ((hs.pow 2).add (continuous_const.mul (continuous_norm.pow 2))).measurable
  · exact (continuous_norm.pow 2).measurable

end RegConeLimit

open RegConeLimit in

theorem RegConeLimit.proof (hFin : ConeBallFinite.Statement) (hInt : ConeFsLogIntegrable.Statement)
    (hNull : ConeHyperplaneNull.Statement) : RegConeLimit.Statement := by
  intro n e h J u hJ ⟨f, hf⟩ hu
  set μ : Measure (EuclideanSpace ℂ (Fin n)) := Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
    with hμ
  have : IsFiniteMeasure (μ.restrict (coneBall h J)) :=
    isFiniteMeasure_restrict.mpr (hFin n e h J f hJ hf).ne
  set K := Real.log (h.norm u ^ 2 + 1) / 2

  have hS : MeasurableSet {y : EuclideanSpace ℂ (Fin n) | ∑ j, u j * h.pointOf y j = 0} := by
    have hp : Continuous fun y : EuclideanSpace ℂ (Fin n) => h.pointOf y := by
      unfold HermNorm.pointOf
      fun_prop
    exact (isClosed_eq (continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((continuous_apply j).comp hp)) continuous_const).measurableSet
  have hae : ∀ᵐ y ∂(μ.restrict (coneBall h J)), ∑ j, u j * h.pointOf y j ≠ 0 := by
    have h0 : μ.restrict (coneBall h J) {y | ∑ j, u j * h.pointOf y j = 0} = 0 := by
      rw [Measure.restrict_apply hS, inter_comm]
      exact hNull n e h J f u hJ hf hu
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with y hy
    exact hy
  have hlim : Tendsto (fun ε => ∫ y in coneBall h J, fsLogReg h u ε (h.pointOf y) ∂μ) (𝓝[>] 0)
      (𝓝 (∫ y in coneBall h J, fsLog h u (h.pointOf y) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => |fsLog h u (h.pointOf y)| + K) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun ε => (measurable_fsLogReg_pointOf h u ε).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
      filter_upwards [hae] with y hy
      rw [Real.norm_eq_abs]
      exact abs_fsLogReg_pointOf_le h u y hε.1 hε.2.le hy
    · exact (hInt n e h J f u hJ hf hu).abs.add (integrable_const K)
    · filter_upwards [hae] with y hy
      have hy0 : 0 < h.dualNorm (h.pointOf y) := by
        rw [dualNorm_pointOf]
        rcases (norm_nonneg y).eq_or_lt with h0 | h0
        · have := norm_sum_mul_pointOf_le h u y
          rw [← h0, mul_zero] at this
          exact absurd (norm_le_zero_iff.mp this) hy
        · exact h0
      exact (fsLogReg_tendsto h u (h.pointOf y) hy0 hy).mono_left nhdsWithin_le_nhds
  exact hlim.div_const _

end

end GroundTheory.Heights₂.Heights
