import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerBoundLogRatioHalf
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lower_bound_log_ratio_half : ∀ C : ℝ, ∃ C' : ℝ, ∀ B t x h : ℝ, 2 ≤ B → 0 < t → t ≤ 1 / 2 → 0 ≤ x → t / 4 * x - C * Real.log (2 + x) - C * Real.log B - C ≤ h → -(C' * Real.log (B / t ^ 2)) ≤ h := by
  first | exact @GlobalTheory.neg_mul_log_div_sq_le_of_linear_sub_log_le | exact GlobalTheory.neg_mul_log_div_sq_le_of_linear_sub_log_le | (intros; apply GlobalTheory.neg_mul_log_div_sq_le_of_linear_sub_log_le <;> assumption)
