import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepIntPolyRootModPrimeSq
open scoped TensorProduct Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_large_prime_sq_dvd_eval_of_separable : ∀ f : ℤ[X], 0 < f.natDegree → (f.map (Int.castRingHom ℚ)).Separable → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, ((p : ℤ) ^ 2) ∣ f.eval x := by
  first | exact @GlobalTheory.sep_int_poly_root_mod_prime_sq | exact GlobalTheory.sep_int_poly_root_mod_prime_sq | (intros; apply GlobalTheory.sep_int_poly_root_mod_prime_sq <;> assumption)
