import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLeastSquaresBound
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_weighted_least_squares_le : ∀ (M g : ℕ) (L : Matrix (Fin M) (Fin g) ℝ), L.rank = g → ∃ K : ℝ, ∀ (D : Fin M → ℝ) (b : Fin M → ℝ), (∀ k, 0 < D k) → ‖((L.transpose * Matrix.diagonal D * L)⁻¹ * L.transpose * Matrix.diagonal D).mulVec b‖ ≤ K * ‖b‖ := by
  first | exact @GlobalTheory.WeightedLS.weighted_least_squares_bound | exact GlobalTheory.WeightedLS.weighted_least_squares_bound | (intros; apply GlobalTheory.WeightedLS.weighted_least_squares_bound <;> assumption)
