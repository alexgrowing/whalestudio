import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivIntegralCompactSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deriv_integral_compact_support : ∀ {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (ρ : ℝ → Mat n → ℝ), Sm ρ → ∀ (K : Set (G n)), IsCompact K → ∀ (s₀ ε : ℝ), 0 < ε → (∀ s ∈ Metric.ball s₀ ε, ∀ y : G n, y ∉ K → ρ s y.val = 0) → HasDerivAt (fun s => ∫ y : G n, ρ s y.val ∂μ) (∫ y : G n, dt ρ s₀ y.val ∂μ) s₀ := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.IntDeriv.hasDerivAt_integral_compact | exact GlobalTheory.CompanionTheory.WaveSpd.IntDeriv.hasDerivAt_integral_compact | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.IntDeriv.hasDerivAt_integral_compact <;> assumption)
