import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ScaledBoundInequalityHypothesesOne

namespace PI.UnitaryGroupMassFormula.TBNum

open ComplexConjugate

theorem schwarzBall : ReciprocityTheory.ChartRestriction.G.TB.SchwarzBallSt := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.SchwarzBallSt
  intro E _ _ u ρ M hρ hu hM z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hzρ : ‖z‖ < ρ := mem_ball_zero_iff.mp hz
  have hmaps : Set.MapsTo (fun w : ℂ => w • z) (Metric.ball 0 (ρ / ‖z‖)) (Metric.ball (0 : E) ρ) := by
    intro w hw
    rw [mem_ball_zero_iff] at hw ⊢
    rw [norm_smul]
    rw [lt_div_iff₀ hzpos] at hw
    exact hw
  have hg : DifferentiableOn ℂ (fun w : ℂ => u (w • z)) (Metric.ball 0 (ρ / ‖z‖)) :=
    hu.comp (differentiable_id.smul_const z).differentiableOn hmaps
  have h1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) (ρ / ‖z‖) := by
    rw [mem_ball_zero_iff, norm_one, lt_div_iff₀ hzpos, one_mul]
    exact hzρ
  have hmap2 : Set.MapsTo (fun w : ℂ => u (w • z)) (Metric.ball 0 (ρ / ‖z‖))
      (Metric.closedBall (u ((0 : ℂ) • z)) M) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm, zero_smul]
    exact hM _ (hmaps hw)
  have hS := Complex.dist_le_div_mul_dist_of_mapsTo_ball hg hmap2 h1
  simp only [one_smul, zero_smul, dist_eq_norm, sub_zero, norm_one, mul_one] at hS
  rw [div_div_eq_mul_div] at hS
  exact hS

end PI.UnitaryGroupMassFormula.TBNum
