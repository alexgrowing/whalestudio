import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLargePrimeDvdIntPolynomialEval
open scoped TensorProduct Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_large_prime_dvd_int_polynomial_eval : ∀ f : ℤ[X], 0 < f.natDegree → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, (p : ℤ) ∣ f.eval x := by
  first | exact @GlobalTheory.exists_prime_gt_dvd_eval | exact GlobalTheory.exists_prime_gt_dvd_eval | (intros; apply GlobalTheory.exists_prime_gt_dvd_eval <;> assumption)
