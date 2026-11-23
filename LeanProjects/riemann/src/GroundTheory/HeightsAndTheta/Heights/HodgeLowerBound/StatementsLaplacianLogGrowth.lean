import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian Real

def LaplacianLogGrowth.Statement : Prop :=
  ∀ (u F : ℂ → ℝ) (a r : ℝ), ContDiff ℝ 2 u → 0 < r → ContDiffOn ℝ 2 F (Metric.ball 0 r) →
    (∀ y : ℂ, r⁻¹ < ‖y‖ → u y = a * Real.log ‖y‖ + F y⁻¹) →
    MeasureTheory.Integrable (Δ u) ∧ ∫ y, Δ u y = 2 * π * a

def fsPotPlane (y : ℂ) : ℝ := Real.log (1 + ‖y‖ ^ 2) / 2

theorem contDiff_fsPotPlane : ContDiff ℝ 2 fsPotPlane := by
  unfold fsPotPlane
  exact ((contDiff_const.add (contDiff_norm_sq ℝ)).log fun y => by positivity).div_const _

theorem fsPotPlane_eq {y : ℂ} (hy : 1⁻¹ < ‖y‖) : fsPotPlane y = 1 * Real.log ‖y‖ + fsPotPlane y⁻¹ := by
  have hy0 : 0 < ‖y‖ := lt_trans (by norm_num) hy
  unfold fsPotPlane
  rw [norm_inv]
  have h1 : 1 + ‖y‖ ^ 2 = ‖y‖ ^ 2 * (1 + ‖y‖⁻¹ ^ 2) := by
    field_simp
    ring
  rw [h1, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  push_cast
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
