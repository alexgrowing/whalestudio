import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTimeRightDerivativesCommute
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_time_right_derivatives_commute : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (u : ℝ → Mat n → W), Sm u → Sm (dt u) ∧ (∀ X : Mat n, Sm (Rt X u)) ∧ (∀ s, ContDiffOn ℝ ∞ (u s) (GLs n)) ∧ (∀ y ∈ GLs n, ContDiff ℝ ∞ fun s => u s y) ∧ ∀ (X : Mat n) (s : ℝ), ∀ y ∈ GLs n, dt (Rt X u) s y = Rr X (dt u s) y := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.sm_calculus | exact GlobalTheory.CompanionTheory.WaveSpd.sm_calculus | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.sm_calculus <;> assumption)
