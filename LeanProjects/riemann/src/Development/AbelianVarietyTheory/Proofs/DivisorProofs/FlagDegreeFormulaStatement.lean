import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeFormula
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_degree_formula : Formalism.DegreeFormula.FlagDegFormula := by
  first | exact @GlobalTheory.FlagPoly.flagDegFormula | exact GlobalTheory.FlagPoly.flagDegFormula | (intros; apply GlobalTheory.FlagPoly.flagDegFormula <;> assumption)
