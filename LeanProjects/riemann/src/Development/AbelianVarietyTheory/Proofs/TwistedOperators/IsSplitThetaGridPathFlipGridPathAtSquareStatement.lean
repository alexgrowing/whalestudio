import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSplitThetaGridPathFlipGridPathAtSquare
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
open GlobalTheory.SplitFlip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSplitThetaGridPath_flipGridPathAtSquare : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ → IsPath (flipPath i j γ) := by
  first | exact @GlobalTheory.SplitFlip.isPath_flipPath | exact GlobalTheory.SplitFlip.isPath_flipPath | (intros; apply GlobalTheory.SplitFlip.isPath_flipPath <;> assumption)
