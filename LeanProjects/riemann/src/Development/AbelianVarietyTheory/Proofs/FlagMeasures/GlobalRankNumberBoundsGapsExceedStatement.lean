import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsGapsExceed
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
open GlobalTheory.Diag.PG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalRankNumberBounds_gaps_exceed : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → ∀ r : ℝ, k ≤ r → r ≤ 2 * k → C * k * m ^ 4 + r * m ^ 10 < 4 * Del ∧ C * k * m ^ 4 + r * m ^ 10 < Real.sqrt (bx x eps) ∧ C * k * m ^ 4 + r * m ^ 10 < x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps ∧ C * r ^ 19 * f ^ 5 * x ^ eps ≤ x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
  first | exact @GlobalTheory.Diag.PG.gaps_exceed | exact GlobalTheory.Diag.PG.gaps_exceed | (intros; apply GlobalTheory.Diag.PG.gaps_exceed <;> assumption)
