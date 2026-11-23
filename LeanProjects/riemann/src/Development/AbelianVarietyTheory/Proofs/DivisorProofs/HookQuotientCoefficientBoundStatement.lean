import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookQuotientCoefficientBound
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hook_quotient_coefficient_bound : ∀ (N k : ℕ), 1 ≤ k → k ≤ N → ∃ rr : MvPolynomial (Fin N) ℝ, rr.IsHomogeneous k ∧ hookR N k = rr * detE (rho N) ∧ ∑ m ∈ rr.support, |rr.coeff m| ≤ 2 ^ (k - 1) / (k.factorial : ℝ) := by
  first | exact @GlobalTheory.FlagHook.exists_hookR_eq_mul_detE_rho | exact GlobalTheory.FlagHook.exists_hookR_eq_mul_detE_rho | (intros; apply GlobalTheory.FlagHook.exists_hookR_eq_mul_detE_rho <;> assumption)
