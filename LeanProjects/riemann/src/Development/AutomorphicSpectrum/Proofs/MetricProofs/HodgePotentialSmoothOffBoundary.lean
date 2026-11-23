import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.MuPotentialSmoothOffBoundary
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hodge_potential_smooth_off_boundary : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D), (∀ a, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => phMu Hd ((D.chart a).γ t)) (offBd D a)) ∧ ∀ a, ∀ t₀ : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ, ‖t₀‖ ≤ 1 / 2 → ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ t ∈ offBd D a, ‖t - t₀‖ < ε → -(C * Real.log ((D.chart a).logR t)) ≤ phMu Hd ((D.chart a).γ t) ∧ phMu Hd ((D.chart a).γ t) ≤ C ∧ ‖fderiv ℝ (fun s => phMu Hd ((D.chart a).γ s)) t‖ ≤ C * (D.chart a).logR t ^ C * Real.exp ((D.chart a).logR t / 2) := by
  first | exact @LevelTowerAlt.mu_potential_smooth_off_boundary | exact LevelTowerAlt.mu_potential_smooth_off_boundary
