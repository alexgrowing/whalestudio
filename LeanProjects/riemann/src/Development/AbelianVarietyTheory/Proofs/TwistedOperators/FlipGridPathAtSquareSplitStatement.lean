import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlipGridPathAtSquareSplit
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
open GlobalTheory.SplitFlip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flipGridPathAtSquare_split : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ → ∃ l₁ l₂ : List Edge, γ = l₁ ++ [Edge.theta i j, Edge.ex i j] ++ l₂ ∧ flipPath i j γ = l₁ ++ [Edge.ex i (j + 1), Edge.theta (i + 1) j] ++ l₂ := by
  first | exact @GlobalTheory.SplitFlip.flipPath_split | exact GlobalTheory.SplitFlip.flipPath_split | (intros; apply GlobalTheory.SplitFlip.flipPath_split <;> assumption)
