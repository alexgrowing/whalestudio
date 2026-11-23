import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingCoefficientFormula
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternating_coefficient_formula : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (n : ι → Fin N → ℕ) (u : ι → Fin N → ℝ) (τ' : ι) (i : Fin N) (m M : ℕ), M + m = ∑ τ, ∑ c, n τ c → altCoeff n (X (τ', i) ^ m * linRoot u ^ M) = (-1) ^ (dimFl ι N + M) * (M.factorial : ℝ) * (eval (u τ') ((pderiv i)^[m] (detE (n τ'))) * ∏ τ ∈ univ.erase τ', eval (u τ) (detE (n τ))) := by
  first | exact @GlobalTheory.AltCoeffPow.altCoeff_X_pow_mul_linRoot_pow | exact GlobalTheory.AltCoeffPow.altCoeff_X_pow_mul_linRoot_pow | (intros; apply GlobalTheory.AltCoeffPow.altCoeff_X_pow_mul_linRoot_pow <;> assumption)
