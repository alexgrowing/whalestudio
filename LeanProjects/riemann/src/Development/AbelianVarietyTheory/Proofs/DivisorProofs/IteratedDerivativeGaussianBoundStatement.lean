import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivativeGaussianBound
import Mathlib
open MeasureTheory
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iterated_derivative_gaussian_bound : ∀ (f : ℂ → ℂ) (a S : ℝ) (n i : ℕ), Differentiable ℂ f → 0 ≤ a → 1 ≤ n → (∀ t : ℂ, ‖f t‖ ^ 2 ≤ S ^ 2 * Real.exp (n * a * ‖t‖ ^ 2)) → ‖iteratedDeriv i f 0‖ ^ 2 ≤ (√(Real.exp 1 * n * i) ^ i * √a ^ i) ^ 2 * S ^ 2 := by
  first | exact @GlobalTheory.norm_iteratedDeriv_sq_le_of_gaussian_growth | exact GlobalTheory.norm_iteratedDeriv_sq_le_of_gaussian_growth | (intros; apply GlobalTheory.norm_iteratedDeriv_sq_le_of_gaussian_growth <;> assumption)
