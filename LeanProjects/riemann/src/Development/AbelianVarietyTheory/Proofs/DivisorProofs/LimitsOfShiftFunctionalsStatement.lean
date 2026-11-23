import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitsOfShiftFunctionals
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limits_of_shift_functionals : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) [Nonempty ι] (j : ℕ) (a b : ℕ → ℝ), 1 ≤ j → j < N → (∀ F : Pol ι N, F.IsHomogeneous (dimFl ι N + 1) → ∃ L : ℝ, Filter.Tendsto (fun B => a B * (∑ τ, shF j τ F) + b B * (∑ τ, totF τ F)) Filter.atTop (nhds L)) → ∃ A b₀ : ℝ, Filter.Tendsto a Filter.atTop (nhds A) ∧ Filter.Tendsto b Filter.atTop (nhds b₀) := by
  first | exact @GlobalTheory.FlagPoly.coefficients_converge | exact GlobalTheory.FlagPoly.coefficients_converge | (intros; apply GlobalTheory.FlagPoly.coefficients_converge <;> assumption)
