import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitThetaGridPathAvoidsOppositeCorner
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
open GlobalTheory.SplitFlip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitThetaGridPath_avoids_opposite_corner : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ → ∀ b ∈ γ, b.src ≠ (i + 1, j + 1) ∧ b.tgt ≠ (i + 1, j + 1) := by
  first | exact @GlobalTheory.SplitFlip.pathAvoid | exact GlobalTheory.SplitFlip.pathAvoid | (intros; apply GlobalTheory.SplitFlip.pathAvoid <;> assumption)
