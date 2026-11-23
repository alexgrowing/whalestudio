import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateRightDerivative
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DwCons
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.left_translate_right_derivative : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
    ContDiffOn ℝ ∞ f (GLs n) → ∀ x ∈ GLs n, ContDiffOn ℝ ∞ (fun y => f (x * y)) (GLs n) ∧
      ∀ (w : List (Idx n)), ∀ y ∈ GLs n, Rw w (fun y => f (x * y)) y = Rw w f (x * y) := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.LeftTr.Rw_left | exact GlobalTheory.CompanionTheory.SobGL.LeftTr.Rw_left | (intros; apply GlobalTheory.CompanionTheory.SobGL.LeftTr.Rw_left <;> assumption)
