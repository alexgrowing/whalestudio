import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeEqDiscriminantMultiple
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_degree_eq_discriminant_multiple : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ lam : ι → Fin N → ℝ, flagDeg ι N lam = c * ev lam (delPol ι N) := by
  first | exact @GlobalTheory.FlagPoly.flagDeg_eq_pos_mul_delPol | exact GlobalTheory.FlagPoly.flagDeg_eq_pos_mul_delPol | (intros; apply GlobalTheory.FlagPoly.flagDeg_eq_pos_mul_delPol <;> assumption)
