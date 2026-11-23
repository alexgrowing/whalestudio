import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonReproducesHarmonic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polydisc_poisson_reproduces_harmonic : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℝ) (ρ R M : ℝ), 0 < ρ → ρ < R → ContinuousOn f (punct R) → SepHarm R f → (∀ z ∈ punct R, |f z| ≤ M) → ∀ z ∈ punct ρ, polyPoisson ρ f z = f z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.polyPoisson_eq_self | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.polyPoisson_eq_self | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.polyPoisson_eq_self <;> assumption)
