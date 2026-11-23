import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodGramComparisonBound
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_gram_comparison_bound : ∀ (n a₀ g r a : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ g Λ) (U : Fin r → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ) (π : Equiv.Perm (Fin n)) (ρ : ℝ), 0 < ρ → ρ ≤ 1 → (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) → LinearIndependent ℂ (fun k => U k 0) → (∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < a ∧ t₀ (π.symm i) = 0) → ∃ ε c C : ℝ, 0 < ε ∧ ε ≤ ρ ∧ 0 < c ∧ 0 < C ∧ ∀ t : Fin n → ℂ, ‖t - t₀‖ < ε → ‖t‖ < 1 → HodgeMetric.uncentre t₀ ρ π t ∈ Flat.punct n a₀ 1 → ((HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t))⁻¹ - (c : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)).PosSemidef ∧ (((C * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - (HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t))⁻¹).PosSemidef ∧ ∀ p q, ‖fderiv ℝ (fun t' => HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t') p q) t‖ ≤ C * Real.exp ((Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.logBound_recentred | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.logBound_recentred | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.logBound_recentred <;> assumption)
