import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookFunctionalPowerSum
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hook_functional_power_sum : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (τ : ι) (k : ℕ) (G : MvPolynomial (ι × Fin N) ℝ), 1 ≤ k → k ≤ N → G.IsHomogeneous (dimFl ι N) → hookFl τ k (pw N τ k * G) = degFl ι N G := by
  first | exact @GlobalTheory.FlagHook.HookPow.hookFl_pw_mul | exact GlobalTheory.FlagHook.HookPow.hookFl_pw_mul | (intros; apply GlobalTheory.FlagHook.HookPow.hookFl_pw_mul <;> assumption)
