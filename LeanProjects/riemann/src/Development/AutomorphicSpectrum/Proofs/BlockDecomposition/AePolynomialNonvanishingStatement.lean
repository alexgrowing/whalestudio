import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AePolynomialNonvanishing
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ae_polynomial_nonvanishing : ∀ (M n : ℕ) (Q : MvPolynomial (Fin M × Fin n) ℂ), Q ≠ 0 → ∀ᵐ C ∂(volume : Measure (Fin M → Fin n → ℂ)), MvPolynomial.eval (fun p => C p.1 p.2) Q ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.AePoly.ae_eval_matrix_ne_zero | exact GlobalTheory.CompanionTheory.AePoly.ae_eval_matrix_ne_zero | (intros; apply GlobalTheory.CompanionTheory.AePoly.ae_eval_matrix_ne_zero <;> assumption)
