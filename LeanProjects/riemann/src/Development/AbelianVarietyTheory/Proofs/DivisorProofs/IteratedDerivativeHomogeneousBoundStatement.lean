import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivativeHomogeneousBound
open MvPolynomial Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iterated_derivative_homogeneous_bound : ∀ (N k n : ℕ) (rr : MvPolynomial (Fin N) ℝ) (i : Fin N) (U : ℝ) (v : Fin N → ℝ), rr.IsHomogeneous k → n ≤ k → 0 ≤ U → (∀ a, |v a| ≤ U) → |eval v ((pderiv i)^[n] rr)| ≤ (∑ m ∈ rr.support, |rr.coeff m|) * (k : ℝ) ^ n * U ^ (k - n) := by
  first | exact @GlobalTheory.abs_eval_iterate_pderiv_homogeneous_le | exact GlobalTheory.abs_eval_iterate_pderiv_homogeneous_le | (intros; apply GlobalTheory.abs_eval_iterate_pderiv_homogeneous_le <;> assumption)
