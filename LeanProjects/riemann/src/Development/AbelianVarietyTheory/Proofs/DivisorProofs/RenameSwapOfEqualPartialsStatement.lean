import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RenameSwapOfEqualPartials
import Mathlib
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rename_swap_of_equal_partials : ∀ (n : ℕ) (i i' : Fin (n + 1)) (K : MvPolynomial (Fin (n + 1)) ℝ), pderiv i' K = pderiv i K → rename (Equiv.swap i i') K = K := by
  first | exact @GlobalTheory.rename_swap_eq_of_pderiv_eq | exact GlobalTheory.rename_swap_eq_of_pderiv_eq | (intros; apply GlobalTheory.rename_swap_eq_of_pderiv_eq <;> assumption)
