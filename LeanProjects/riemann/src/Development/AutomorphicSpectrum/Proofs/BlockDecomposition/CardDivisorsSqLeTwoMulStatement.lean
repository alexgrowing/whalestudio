import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardDivisorsSqLeTwoMul
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_divisors_sq_le_two_mul' : ∀ n : ℕ, (((n ^ 2).divisors.card : ℕ) : ℝ) ≤ 2 * n := by
  first | exact @GlobalTheory.CompanionTheory.DivisorCount.card_divisors_sq_le_two_mul | exact GlobalTheory.CompanionTheory.DivisorCount.card_divisors_sq_le_two_mul | (intros; apply GlobalTheory.CompanionTheory.DivisorCount.card_divisors_sq_le_two_mul <;> assumption)
