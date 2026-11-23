import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumTwoPowPredMulExpNegLeExpNegThird
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_two_pow_pred_mul_exp_neg_le_exp_neg_third : ∀ (q : ℕ) (x : ℝ), 15 ≤ x → ∑ J ∈ Finset.Icc 1 q, (2 : ℝ) ^ (J - 1) * Real.exp (-(1 / 2 * J * x)) ≤ Real.exp (-(1 / 3 * x)) := by
  first | exact @GlobalTheory.sum_two_pow_pred_mul_exp_neg_le | exact GlobalTheory.sum_two_pow_pred_mul_exp_neg_le | (intros; apply GlobalTheory.sum_two_pow_pred_mul_exp_neg_le <;> assumption)
