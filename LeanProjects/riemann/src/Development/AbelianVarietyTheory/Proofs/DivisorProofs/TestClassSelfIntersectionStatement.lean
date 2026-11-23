import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestClassSelfIntersection
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_class_self_intersection : ∀ (D : D7) (Y : ShimX D.what₂.Tau), Propor Y → let Q : D.what₂.Tau → ℕ → Pol D.what₂.Tau Y.N := fun _ k => if k = 2 then curveCl D.what₂.Tau Y.N Y.j else 0; Cof Y Q ∧ comb Y Q = testF Y ∧ testI Y < 0 ∧ shAll Y (testF Y) = 2 * testI Y ∧ totAll Y (testF Y) = 0 ∧ ∀ p : ℕ, 2 ≤ p → restTerm Y p Q = 2 * testI Y * Y.vol * (Real.log p / ((p : ℝ) ^ 2 - 1)) := by
  first | exact @GlobalTheory.RestTest.restTerm_testClass | exact GlobalTheory.RestTest.restTerm_testClass | (intros; apply GlobalTheory.RestTest.restTerm_testClass <;> assumption)
