import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqPrimePowMulNotDvdCompletedLaurent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_prime_pow_mul_not_dvd_O0 : ∀ (p : ℕ) [Fact p.Prime], ∀ x : O0 p, x ≠ 0 → ∃ (k : ℕ) (y : O0 p), x = (p : O0 p) ^ k * y ∧ ¬ (p : O0 p) ∣ y := by
  first | exact @GlobalTheory.K5.Basic.exists_eq_prime_pow_mul_not_dvd_completedLaurent | exact GlobalTheory.K5.Basic.exists_eq_prime_pow_mul_not_dvd_completedLaurent | (intros; apply GlobalTheory.K5.Basic.exists_eq_prime_pow_mul_not_dvd_completedLaurent <;> assumption)
