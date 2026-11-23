import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaFormulaHookSchur
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappa_formula_hook_schur : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (u : ι → Fin N → ℝ) (Q : ι → ℕ → MvPolynomial (ι × Fin N) ℝ), (∀ τ a b, a ≠ b → u τ a ≠ u τ b) → IsDecomp u Q → ∀ (τ τ' : ι) (i : Fin N) (k : ℕ), 1 ≤ k → k ≤ N → kap u k (X (τ', i) ^ (k - 1)) (Q τ k) = if τ' = τ then -(eval (u τ) ((pderiv i)^[k - 1] (hookR N k)) / eval (u τ) (detE (rho N))) else -(eval (u τ) (hookR N k) / eval (u τ) (detE (rho N)) * (eval (u τ') ((pderiv i)^[k - 1] (detE (rho N))) / eval (u τ') (detE (rho N)))) := by
  first | exact @GlobalTheory.FlagHook.KapFormula.kap_formula | exact GlobalTheory.FlagHook.KapFormula.kap_formula | (intros; apply GlobalTheory.FlagHook.KapFormula.kap_formula <;> assumption)
