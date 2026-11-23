import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsSizeComparisons
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
open GlobalTheory.Diag.PG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalRankNumberBounds_size_comparisons : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → 1 ≤ Del ∧ C * (m * k * Del) ≤ Real.sqrt (bx x eps) ∧ max (k ^ C) (bx x eps ^ ((1 : ℝ) / 4)) ≤ Real.sqrt (bx x eps) ∧ 12 * k * Del ≤ Real.sqrt (bx x eps) ∧ Real.sqrt (bx x eps) ≤ bx x eps ^ 2 ∧ bx x eps ^ 2 ≤ bx x eps ^ (3 : ℝ) ∧ (C ≤ CD → (k * f * x ^ eps) ^ C ≤ Del) := by
  first | exact @GlobalTheory.Diag.PG.SqrtBound.rankNums_sizes | exact GlobalTheory.Diag.PG.SqrtBound.rankNums_sizes | (intros; apply GlobalTheory.Diag.PG.SqrtBound.rankNums_sizes <;> assumption)
