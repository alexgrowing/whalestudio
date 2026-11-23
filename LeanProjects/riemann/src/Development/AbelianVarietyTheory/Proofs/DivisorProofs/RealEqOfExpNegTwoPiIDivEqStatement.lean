import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealEqOfExpNegTwoPiIDivEq
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_forall_cexp_neg_two_pi_I_mul_div_eq : ∀ x y : ℝ, (∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (y : ℂ) / k)) →
    x = y := by
  first | exact @GlobalTheory.real_eq_of_exp_neg_two_pi_I_div_eq | exact GlobalTheory.real_eq_of_exp_neg_two_pi_I_div_eq | (intros; apply GlobalTheory.real_eq_of_exp_neg_two_pi_I_div_eq <;> assumption)
