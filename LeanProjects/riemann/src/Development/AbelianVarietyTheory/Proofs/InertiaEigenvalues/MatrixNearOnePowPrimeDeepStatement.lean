import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixNearOnePowPrimeDeep
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sub_one_le_of_norm_pow_prime_sub_one_le : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (X : Matrix n n ℚ_[l]) (k : ℕ), (∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-2 : ℤ)) → (∀ i j, ‖(X ^ l - 1) i j‖ ≤ (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2))) → ∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) := by
  first | exact @GlobalTheory.matrix_near_one_pow_prime_deep | exact GlobalTheory.matrix_near_one_pow_prime_deep | (intros; apply GlobalTheory.matrix_near_one_pow_prime_deep <;> assumption)
