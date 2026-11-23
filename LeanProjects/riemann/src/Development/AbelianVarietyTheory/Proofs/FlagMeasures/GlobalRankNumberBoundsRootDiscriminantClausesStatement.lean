import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsRootDiscriminantClauses
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
open GlobalTheory.Diag.PG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalRankNumberBounds_rootDiscriminant_clauses : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → C * (m * (lrd - Real.log 2)) ≤ k ∧ C * (m ^ 3 * x ^ eps * lrd) ≤ k * Real.log k ^ 2 ∧ lrd ≤ x ^ eps / C := by
  first | exact @GlobalTheory.Diag.PG.rankNums_rootDisc | exact GlobalTheory.Diag.PG.rankNums_rootDisc | (intros; apply GlobalTheory.Diag.PG.rankNums_rootDisc <;> assumption)
