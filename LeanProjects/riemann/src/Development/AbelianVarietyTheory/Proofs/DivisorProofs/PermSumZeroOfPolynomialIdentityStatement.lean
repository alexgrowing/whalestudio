import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermSumZeroOfPolynomialIdentity
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perm_sum_zero_of_polynomial_identity : ∀ (D : ℕ) (E : (Fin D → Fin D) → ℝ), (∀ n : Fin D → ℤ, ∑ a : Fin D → Fin D, (∏ j, (n (a j) : ℝ)) * E a = 0) → ∑ σ : Equiv.Perm (Fin D), E σ = 0 := by
  first | exact @GlobalTheory.sum_perm_eq_zero_of_polarisation | exact GlobalTheory.sum_perm_eq_zero_of_polarisation | (intros; apply GlobalTheory.sum_perm_eq_zero_of_polarisation <;> assumption)
