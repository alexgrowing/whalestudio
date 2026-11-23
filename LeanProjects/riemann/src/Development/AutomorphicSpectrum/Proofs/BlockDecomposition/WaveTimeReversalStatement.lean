import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveTimeReversal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wave_time_reversal : ∀ {n : ℕ} (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → IsWave E fun s => u (-s) := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.isWave_time_refl | exact GlobalTheory.CompanionTheory.WaveSpd.isWave_time_refl | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.isWave_time_refl <;> assumption)
