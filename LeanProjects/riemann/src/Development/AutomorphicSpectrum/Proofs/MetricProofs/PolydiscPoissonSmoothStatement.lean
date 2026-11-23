import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonSmooth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polydisc_poisson_smooth : ∀ (n : ℕ) (ρ : ℝ) (h : (Fin n → ℂ) → ℝ), 0 < ρ → Continuous (fun θ : Fin n → ℝ => h (torusPt ρ θ)) → ContDiffOn ℝ ∞ (polyPoisson ρ h) (Metric.ball 0 ρ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.Smooth.contDiffOn_polyPoisson | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.Smooth.contDiffOn_polyPoisson | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.Smooth.contDiffOn_polyPoisson <;> assumption)
