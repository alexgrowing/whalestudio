import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookFunctionalPowerSumOther
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hook_functional_power_sum_other : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (τ τ'' : ι) (k k' : ℕ) (G : MvPolynomial (ι × Fin N) ℝ), 1 ≤ k → k ≤ N → 1 ≤ k' → (τ'', k') ≠ (τ, k) → hookFl τ k (pw N τ'' k' * G) = 0 := by
  first | exact @GlobalTheory.HookKill.hookFl_pw_mul_eq_zero | exact GlobalTheory.HookKill.hookFl_pw_mul_eq_zero | (intros; apply GlobalTheory.HookKill.hookFl_pw_mul_eq_zero <;> assumption)
