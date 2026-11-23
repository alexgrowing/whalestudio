import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerBoundLogRatioUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lower_bound_log_ratio_unit : ∀ C : ℝ, 1 ≤ C → ∃ C' : ℝ, ∀ B s x h : ℝ, 2 ≤ B → 0 < s → s ≤ 1 → -C ≤ x → s * x - C * Real.log (2 + C + x) - C * Real.log (B / s) - C ≤ h → -(C' * Real.log (B / s)) ≤ h := by
  first | exact @GlobalTheory.boundary_lower_bound_numerical | exact GlobalTheory.boundary_lower_bound_numerical | (intros; apply GlobalTheory.boundary_lower_bound_numerical <;> assumption)
