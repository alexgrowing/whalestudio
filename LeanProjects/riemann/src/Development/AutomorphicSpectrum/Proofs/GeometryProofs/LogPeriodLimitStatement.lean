import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_period_limit : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ), ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ (ws : ℕ → Fin n → ℂ) (W : Submodule ℤ Λ) (per : W →+ (Fin g → ℂ)), (∀ m, ws m ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le) ∧ Tendsto (fun m => GroundTheory.Heights₂.Heights.Regular.expCover a (ws m)) atTop (𝓝 z) ∧ (∀ x : W, Tendsto (fun m => L.P (ws m) x) atTop (𝓝 (per x))) ∧ (∀ (x : ℕ → Λ) (p : Fin g → ℂ), Tendsto (fun m => L.P (ws m) (x m)) atTop (𝓝 p) → ∃ x₀ : W, p = per x₀ ∧ ∀ᶠ m in atTop, x m = x₀) ∧ (∀ φ : W →+ ℤ, (∀ x : W, (∀ x' : W, L.E x x' = 0) → φ x = 0) → ∃ x₀ : W, ∀ x : W, φ x = L.E x₀ x) ∧ ∀ Hb : Matrix (Fin g) (Fin g) ℂ, Hb.IsHermitian → (∀ x x' : W, (per x ⬝ᵥ Hb *ᵥ star (per x')).im = L.E x x') → (∀ x : W, (∀ x' : W, L.E x x' = 0) → Hb *ᵥ star (per x) = 0) → ∀ v : Fin g → ℂ, 0 ≤ (v ⬝ᵥ Hb *ᵥ star v).re ∧ (v ⬝ᵥ Hb *ᵥ star v).re ≤ C * ∑ i, ‖v i‖ ^ 2 ∧ ((v ⬝ᵥ Hb *ᵥ star v).re = 0 → v ∈ Submodule.span ℂ {p | ∃ x : W, (∀ x' : W, L.E x x' = 0) ∧ p = per x}) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RiemannLimit.bounded_on_limit_lattice | exact GlobalTheory.CompanionTheory.Ar.RiemannLimit.bounded_on_limit_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.RiemannLimit.bounded_on_limit_lattice <;> assumption)
