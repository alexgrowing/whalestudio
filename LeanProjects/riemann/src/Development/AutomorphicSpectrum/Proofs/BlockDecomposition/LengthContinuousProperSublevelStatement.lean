import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthContinuousProperSublevel
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DwCons
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_continuous_proper_sublevel : ∀ n : ℕ, ContinuousOn (lg (n := n)) (GLs n) ∧ ∀ R : ℝ, IsCompact {y : G n | lg y.val ≤ R} := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.lg_continuousOn_and_isCompact | exact GlobalTheory.CompanionTheory.SobGL.lg_continuousOn_and_isCompact | (intros; apply GlobalTheory.CompanionTheory.SobGL.lg_continuousOn_and_isCompact <;> assumption)
