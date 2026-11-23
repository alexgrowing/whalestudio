import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConeTangentLiftInChart
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_tangent_lift_in_chart : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (a : Fin D.nCharts), ∀ t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, ∀ v, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) ((D.chart a).γ t) v → ∃ (u : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) (c : K → ℂ), v = fderiv ℂ (D.chart a).γ t u + torusSmul c ((D.chart a).γ t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.coneTangent_eq_fderiv_add_torusSmul | exact GlobalTheory.CompanionTheory.Ar.Cusp.coneTangent_eq_fderiv_add_torusSmul | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.coneTangent_eq_fderiv_add_torusSmul <;> assumption)
