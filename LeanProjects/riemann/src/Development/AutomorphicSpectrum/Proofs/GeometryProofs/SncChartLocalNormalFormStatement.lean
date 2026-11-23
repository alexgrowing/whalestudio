import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartLocalNormalForm
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_chart_local_normal_form : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] (y : (Σ k, J k) → Ω) (P : Ideal (MRing J)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : SncChart P n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω), t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 → InFrameDomain y cc f (χ.γ t₀) → ∃ (a₀ : ℕ) (π : Equiv.Perm (Fin n)) (ρ₀ : ℝ), a₀ ≤ n ∧ 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ (∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < χ.a ∧ t₀ (π.symm i) = 0) ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, HodgeMetric.recentre t₀ ρ π u ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ InFrameDomain y cc f (χ.γ (HodgeMetric.recentre t₀ ρ π u)) ∧ (χ.γ (HodgeMetric.recentre t₀ ρ π u) ∉ Bd ↔ u ∈ Flat.punct n a₀ 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartGeo.exists_recentre_chart | exact GlobalTheory.CompanionTheory.Ar.ChartGeo.exists_recentre_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartGeo.exists_recentre_chart <;> assumption)
