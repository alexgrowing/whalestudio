import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassDegreeOne
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_class_degree_one : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (j : ℕ) (τ : ι), 1 ≤ j → j < N → ∃ Q : Pol ι N, Q.IsHomogeneous (dimFl ι N - 1) ∧ degFl ι N (pLow j τ 1 * Q) = 1 := by
  first | exact @GlobalTheory.FlagPoly.exists_dual_pLow_one | exact GlobalTheory.FlagPoly.exists_dual_pLow_one | (intros; apply GlobalTheory.FlagPoly.exists_dual_pLow_one <;> assumption)
