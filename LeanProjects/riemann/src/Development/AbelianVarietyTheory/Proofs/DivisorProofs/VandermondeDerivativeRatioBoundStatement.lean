import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeDerivativeRatioBound
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vandermonde_derivative_ratio_bound : ∀ (N n : ℕ) (v : Fin N → ℝ) (i : Fin N) (g : ℝ), 0 < g → (∀ a b, a ≠ b → v a ≠ v b) → (∀ a, a ≠ i → g ≤ |v i - v a|) → |eval v ((pderiv i)^[n] (detE (rho N))) / eval v (detE (rho N))| ≤ ((N : ℝ) / g) ^ n := by
  first | exact @GlobalTheory.FlagHook.abs_iterate_pderiv_detE_rho_div_le | exact GlobalTheory.FlagHook.abs_iterate_pderiv_detE_rho_div_le | (intros; apply GlobalTheory.FlagHook.abs_iterate_pderiv_detE_rho_div_le <;> assumption)
