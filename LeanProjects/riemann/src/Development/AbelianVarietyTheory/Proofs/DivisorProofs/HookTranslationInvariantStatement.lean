import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookTranslationInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hook_translation_invariant : ∀ (N k : ℕ) (a : ℝ), 2 ≤ k → k ≤ N → aeval (fun i : Fin N => (X i + C a : MvPolynomial (Fin N) ℝ)) (hookR N k) = hookR N k ∧ aeval (fun i : Fin N => (X i + C a : MvPolynomial (Fin N) ℝ)) (detE (rho N)) = detE (rho N) := by
  first | exact @GlobalTheory.FlagHookShift.shift_invariant | exact GlobalTheory.FlagHookShift.shift_invariant | (intros; apply GlobalTheory.FlagHookShift.shift_invariant <;> assumption)
