import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveClassDegreeComputations
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_class_degree_computations : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) [Nonempty ι] (j : ℕ), 1 ≤ j → j < N → let I : ℝ := ∑ τ : ι, degFl ι N (pLow j τ 1 * curveCl ι N j); (∑ σ : ι, shF j σ (∑ τ : ι, pSum τ 2 * curveCl ι N j)) = 2 * I ∧ (∀ σ : ι, totF σ (∑ τ : ι, pSum τ 2 * curveCl ι N j) = 0) ∧ degFl ι N (lamA ι N j ^ dimGr ι N j * fibPt ι N j) = -2 * I ∧ degFl ι N (-lamA ι N j * curveCl ι N j) = 2 * I ∧ (curveCl ι N j).IsHomogeneous (dimFl ι N - 1) := by
  first | exact @GlobalTheory.FlagPoly.TestClass.testClass | exact GlobalTheory.FlagPoly.TestClass.testClass | (intros; apply GlobalTheory.FlagPoly.TestClass.testClass <;> assumption)
