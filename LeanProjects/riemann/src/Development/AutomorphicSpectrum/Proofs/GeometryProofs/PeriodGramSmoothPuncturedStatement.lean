import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodGramSmoothPunctured
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_gram_smooth_punctured : ∀ (n a₀ g r : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ g Λ) (U : Fin r → (Fin n → ℂ) → Fin g → ℂ), (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) → ∀ (p q : Fin r), ∀ u ∈ Flat.punct n a₀ 1, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u' => HodgeMetric.periodGram L U u' p q) u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramSmooth.periodGram_contDiffAt | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramSmooth.periodGram_contDiffAt | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramSmooth.periodGram_contDiffAt <;> assumption)
