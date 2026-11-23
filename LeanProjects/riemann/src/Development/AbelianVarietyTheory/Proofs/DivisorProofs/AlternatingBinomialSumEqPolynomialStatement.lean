import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingBinomialSumEqPolynomial
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open MvPolynomial GlobalTheory.LineForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternating_binomial_sum_eq_polynomial : ∀ m : ℕ, ∑ j ∈ Finset.range (m + 1), C ((-1) ^ j * (m.choose j : ℝ) / (m + j + 1 : ℝ)) * X 0 ^ (m - j) * hs (m + j) = pm m := by
  first | exact @GlobalTheory.LineForm.sum_choose_hs_eq_pm | exact GlobalTheory.LineForm.sum_choose_hs_eq_pm | (intros; apply GlobalTheory.LineForm.sum_choose_hs_eq_pm <;> assumption)
