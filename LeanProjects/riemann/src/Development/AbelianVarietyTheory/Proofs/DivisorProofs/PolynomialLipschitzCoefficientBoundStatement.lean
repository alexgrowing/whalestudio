import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialLipschitzCoefficientBound
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_lipschitz_coefficient_bound : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (d : ℕ), ∃ n : ℝ, 0 ≤ n ∧ ∀ (P : MvPolynomial σ ℝ) (c : ℝ) (a b : σ → ℝ), P.totalDegree ≤ d → (∀ m, |P.coeff m| ≤ c) → ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → |eval a P - eval b P| ≤ n * c * ‖a - b‖ := by
  first | exact @GlobalTheory.exists_lipschitz_eval_of_coeff_le | exact GlobalTheory.exists_lipschitz_eval_of_coeff_le | (intros; apply GlobalTheory.exists_lipschitz_eval_of_coeff_le <;> assumption)
