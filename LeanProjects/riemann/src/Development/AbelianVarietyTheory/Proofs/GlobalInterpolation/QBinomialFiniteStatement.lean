import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QBinomialFinite
import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultipliableTpFactor
open Complex
open scoped Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_range_one_add_mul_pow_two_mul_eq_sum_qBinom : ∀ (s X : ℂ), ‖s‖ < 1 → ∀ m : ℕ, ∏ k ∈ Finset.range m, (1 + X * s ^ (2 * k)) = ∑ k ∈ Finset.range (m + 1), GlobalTheory.JacobiTriple.qBinom (s ^ 2) m k * s ^ (k * (k - 1)) * X ^ k := by
  first | exact @GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite | exact GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite | (intros; apply GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite <;> assumption)
