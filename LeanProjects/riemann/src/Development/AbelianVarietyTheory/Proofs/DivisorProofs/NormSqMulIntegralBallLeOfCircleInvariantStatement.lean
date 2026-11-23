import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqMulIntegralBallLeOfCircleInvariant
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sq_mul_integral_ball_le_of_circle_invariant' : ∀ (n : ℕ) (δ : ℝ) (U : Set (V n)) (f : V n → ℂ) (W : V n → ℝ), 0 < δ → IsOpen U → closedBall 0 δ ⊆ U → DifferentiableOn ℂ f U → ContinuousOn W (closedBall 0 δ) → (∀ w, 0 ≤ W w) → (∀ (θ : ℂ) (w : V n), ‖θ‖ = 1 → W (θ • w) = W w) → ‖f 0‖ ^ 2 * ∫ w in ball (0 : V n) δ, W w ≤ ∫ w in ball (0 : V n) δ, ‖f w‖ ^ 2 * W w := by
  first | exact @GlobalTheory.norm_sq_mul_integral_ball_le_of_circle_invariant | exact GlobalTheory.norm_sq_mul_integral_ball_le_of_circle_invariant | (intros; apply GlobalTheory.norm_sq_mul_integral_ball_le_of_circle_invariant <;> assumption)
