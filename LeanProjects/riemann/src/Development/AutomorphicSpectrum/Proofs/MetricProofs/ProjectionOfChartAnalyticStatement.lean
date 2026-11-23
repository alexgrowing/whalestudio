import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionOfChartAnalytic
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projection_of_chart_analytic : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (a : Fin D.nCharts) (k : Fin M.atlas.n), ∀ t ∈ Metric.ball (0 : Fin D.n → ℂ) 1, M.proj ((D.chart a).γ t) ∈ (M.atlas.chart k).source → AnalyticAt ℂ (fun t' : Fin D.n → ℂ => M.atlas.chart k (M.proj ((D.chart a).γ t'))) t ∧ Function.Bijective (fderiv ℂ (fun t' : Fin D.n → ℂ => M.atlas.chart k (M.proj ((D.chart a).γ t'))) t) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.projection_of_chart_analytic | exact GlobalTheory.CompanionTheory.Relay.projection_of_chart_analytic | (intros; apply GlobalTheory.CompanionTheory.Relay.projection_of_chart_analytic <;> assumption)
