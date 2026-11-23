import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpAndLogPowerLeLinear
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_and_log_power_le_linear : ∀ d : ℕ, ∃ C : ℝ, ∀ s : ℝ, 0 < s → s ≤ 1 → Real.exp (-(s ^ 2)⁻¹ / 3) ≤ C * s ∧ Real.log ((s ^ 2)⁻¹) ^ d / (s ^ 2)⁻¹ ≤ C * s := by
  first | exact @GlobalTheory.exp_neg_and_log_pow_div_le_mul | exact GlobalTheory.exp_neg_and_log_pow_div_le_mul | (intros; apply GlobalTheory.exp_neg_and_log_pow_div_le_mul <;> assumption)
