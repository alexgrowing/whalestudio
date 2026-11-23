import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsRankClausesFirstHalf
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
open GlobalTheory.Diag.PG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_rankNums_imp_parameter_lower_bounds : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → C * m ^ 5 * f * x ^ eps ≤ k ∧ Real.log f ≤ Real.sqrt (m / 2 - 1) ∧ C * x ^ eps ≤ f * Real.log k ∧ C * (m ^ 2 * x ^ eps) ≤ k ∧ C ≤ m ∧ C * x ^ eps ≤ m - 1 ∧ C ≤ k ∧ 1 < x ^ eps := by
  first | exact @GlobalTheory.Diag.PG.rankNums_first_half | exact GlobalTheory.Diag.PG.rankNums_first_half | (intros; apply GlobalTheory.Diag.PG.rankNums_first_half <;> assumption)
