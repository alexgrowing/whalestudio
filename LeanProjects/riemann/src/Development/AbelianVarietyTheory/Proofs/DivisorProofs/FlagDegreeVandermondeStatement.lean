import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeVandermonde
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_degree_vandermonde : (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (u : ι → Fin N → ℝ), flagDeg ι N u = ((dimFl ι N).factorial : ℝ) * ∏ τ, eval (u τ) (detE (rho N))) ∧ ∀ (N : ℕ) (v : Fin N → ℝ), eval v (detE (rho N)) = (∏ a : Fin N, ∏ b ∈ Ioi a, (v a - v b)) / ∏ m ∈ range N, (m.factorial : ℝ) := by
  first | exact @GlobalTheory.FlagHook.Degree.flagDeg_eq_and_product | exact GlobalTheory.FlagHook.Degree.flagDeg_eq_and_product | (intros; apply GlobalTheory.FlagHook.Degree.flagDeg_eq_and_product <;> assumption)
