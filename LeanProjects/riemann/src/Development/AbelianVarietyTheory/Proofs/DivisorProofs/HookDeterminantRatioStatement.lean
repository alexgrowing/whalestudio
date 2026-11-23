import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookDeterminantRatio
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hook_determinant_ratio : ∀ (N k r : ℕ), r < k → k ≤ N → ∃ S : MvPolynomial (Fin N) ℝ, S.IsHomogeneous k ∧ (∀ m, 0 ≤ S.coeff m) ∧ eval (fun _ => 1) S = ((N + k - r - 1).choose k * (k - 1).choose r : ℕ) ∧ Matrix.det (Matrix.of fun i c : Fin N => (X i : MvPolynomial (Fin N) ℝ) ^ hookRho N k r c) = S * Matrix.det (Matrix.of fun i c : Fin N => (X i : MvPolynomial (Fin N) ℝ) ^ rho N c) := by
  first | exact @GlobalTheory.HookSchur.exists_hookSchur | exact GlobalTheory.HookSchur.exists_hookSchur | (intros; apply GlobalTheory.HookSchur.exists_hookSchur <;> assumption)
