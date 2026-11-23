import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceSectionMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix
open scoped ContDiff

noncomputable section

def sliceCut {n : ℕ} (h : HermNorm n) (k : ℕ) (x : Fin n → ℂ) : ℝ :=
  Real.smoothTransition (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1))

namespace SliceCut

variable {n : ℕ} (h : HermNorm n)

theorem continuous_dualNorm : Continuous h.dualNorm := by
  unfold HermNorm.dualNorm
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
  exact ((continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id)).norm.pow 2

theorem norm_coord_le (x : Fin n → ℂ) (i : Fin n) : ‖((h.matᵀ)⁻¹ *ᵥ x) i‖ ≤ h.dualNorm x := by
  unfold HermNorm.dualNorm
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun j => ‖((h.matᵀ)⁻¹ *ᵥ x) j‖ ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ i)

theorem mulVec_inv (x : Fin n → ℂ) : h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (by rw [Matrix.det_transpose]; exact h.isUnit_det),
    Matrix.one_mulVec]

theorem isCompact_sublevel (R : ℝ) : IsCompact {x : Fin n → ℂ | h.dualNorm x ≤ R} := by
  refine ((isCompact_closedBall (0 : Fin n → ℂ) R).image
    (Continuous.matrix_mulVec (A := fun _ => h.matᵀ) continuous_const continuous_id)).of_isClosed_subset
    (isClosed_le (continuous_dualNorm h) continuous_const) fun x hx => ?_
  refine ⟨(h.matᵀ)⁻¹ *ᵥ x, ?_, mulVec_inv h x⟩
  have hR : 0 ≤ R := (Real.sqrt_nonneg _).trans hx
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
  exact fun i => (norm_coord_le h x i).trans hx

theorem mem_Icc (k : ℕ) (x : Fin n → ℂ) : sliceCut h k x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem eq_one_of_lt_one (k : ℕ) {x : Fin n → ℂ} (hx : h.dualNorm x < 1) : sliceCut h k x = 1 := by
  unfold sliceCut
  refine Real.smoothTransition.one_of_one_le ?_
  have hlog : Real.log (h.dualNorm x) ≤ 0 := Real.log_nonpos (Real.sqrt_nonneg _) hx.le
  have : Real.log (h.dualNorm x) / ((k : ℝ) + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hlog (by positivity)
  linarith

theorem contDiff (k : ℕ) : ContDiff ℝ ∞ (sliceCut h k) := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  by_cases hx : x = 0
  · subst hx
    have hU : {y : Fin n → ℂ | h.dualNorm y < 1} ∈ 𝓝 (0 : Fin n → ℂ) := by
      refine (isOpen_lt (continuous_dualNorm h) continuous_const).mem_nhds ?_
      simp [HermNorm.dualNorm]
    exact contDiffAt_const.congr_of_eventuallyEq
      (Filter.mem_of_superset hU fun y hy => eq_one_of_lt_one h k hy)
  · have hlog := (contDiffOn_log_dualNorm h).contDiffAt (isOpen_compl_singleton.mem_nhds hx)
    exact Real.smoothTransition.contDiff.contDiffAt.comp x (contDiffAt_const.sub (hlog.div_const _))

theorem hasCompactSupport (k : ℕ) : HasCompactSupport (sliceCut h k) := by
  refine HasCompactSupport.intro (isCompact_sublevel h (Real.exp (2 * ((k : ℝ) + 1)))) fun x hx => ?_
  simp only [Set.mem_ofPred_eq, not_le] at hx
  unfold sliceCut
  refine Real.smoothTransition.zero_of_nonpos ?_
  have hpos : 0 < h.dualNorm x := (Real.exp_pos _).trans hx
  have hlog : 2 * ((k : ℝ) + 1) < Real.log (h.dualNorm x) := by
    rw [Real.lt_log_iff_exp_lt hpos]; exact hx
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [sub_nonpos, le_div_iff₀ hk]
  linarith

theorem tendsto_one (x : Fin n → ℂ) : Tendsto (fun k => sliceCut h k x) atTop (𝓝 1) := by
  have hdiv : Tendsto (fun k : ℕ => Real.log (h.dualNorm x) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have h2 := (tendsto_const_nhds (x := (2 : ℝ))).sub hdiv
  rw [sub_zero] at h2
  have := (Real.smoothTransition.continuous.tendsto 2).comp h2
  rwa [Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2)] at this

theorem measurable (k : ℕ) : Measurable (sliceCut h k) :=
  (contDiff h k).continuous.measurable

end SliceCut

end

end GroundTheory.Heights₂.Heights
