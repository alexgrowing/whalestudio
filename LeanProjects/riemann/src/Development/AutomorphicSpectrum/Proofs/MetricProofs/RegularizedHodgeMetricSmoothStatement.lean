import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeMetricSmooth
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PositionPot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularized_hodge_metric_smooth : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ), S.IsTied → ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (muReg Hd S B t) ∧ (muReg Hd S B t).a = muTwDeg Hd B ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), Real.log ((muReg Hd S B t).h z) = Real.log (S.ref.h z) + S.regWeight t (M.proj z) + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.muReg_smooth_log | exact GlobalTheory.CompanionTheory.Ar.Cusp.muReg_smooth_log | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.muReg_smooth_log <;> assumption)
