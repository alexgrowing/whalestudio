import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityAsSumExpMinusOne
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.identity_as_sum_exp_minus_one : ∃ (n : ℕ) (a : Fin n → ℝ) (A : Fin n → ℝ → ℂ), (∀ j, Function.HasTemperateGrowth (A j)) ∧
    ∀ t : ℝ, (t : ℂ) = ∑ j, (Complex.exp (Complex.I * ((a j * t : ℝ) : ℂ)) - 1) * A j t := by
  first | exact @GlobalTheory.ExpDivision.exists_division | exact GlobalTheory.ExpDivision.exists_division | (intros; apply GlobalTheory.ExpDivision.exists_division <;> assumption)
