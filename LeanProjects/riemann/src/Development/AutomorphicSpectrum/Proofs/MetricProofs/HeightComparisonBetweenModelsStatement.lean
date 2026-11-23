import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightComparisonBetweenModels
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_comparison_between_models : Top.Given → PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M M' : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (S₁ : LogLogRegularisationSetting M' D.Xo (muLine Hd)) (B : ℕ), IsFullIntersectionSystem II → S.IsTied → S₁.IsTied → ArLimExists Hd S B ∧ arLim Hd S B = arLim Hd S₁ B := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.arLim_exists_eq | exact GlobalTheory.CompanionTheory.Ar.Cusp.arLim_exists_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.arLim_exists_eq <;> assumption)
