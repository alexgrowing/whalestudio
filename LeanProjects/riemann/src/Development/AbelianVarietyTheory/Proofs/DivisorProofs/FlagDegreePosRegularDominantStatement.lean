import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreePosRegularDominant
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_degree_pos_regular_dominant : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (lam : ι → Fin N → ℝ), (RegDom lam → 0 < flagDeg ι N lam) ∧ (Dom lam → 0 ≤ flagDeg ι N lam) := by
  first | exact @GlobalTheory.FlagDegSign.flagDeg_pos_and_nonneg | exact GlobalTheory.FlagDegSign.flagDeg_pos_and_nonneg | (intros; apply GlobalTheory.FlagDegSign.flagDeg_pos_and_nonneg <;> assumption)
