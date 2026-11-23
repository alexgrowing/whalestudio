import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeEqFormDegree
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_degree_eq_form_degree : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (P : Pol ι N), degFl ι N P = formDeg (toForm P) := by
  first | exact @GlobalTheory.FlagFormDeg.degFl_eq_formDeg | exact GlobalTheory.FlagFormDeg.degFl_eq_formDeg | (intros; apply GlobalTheory.FlagFormDeg.degFl_eq_formDeg <;> assumption)
