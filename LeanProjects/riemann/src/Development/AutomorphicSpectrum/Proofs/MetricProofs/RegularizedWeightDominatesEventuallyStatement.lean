import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightDominatesEventually
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularized_weight_dominates_eventually : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w), S'.IsTied → ∀ᶠ t' in 𝓝[>] (0 : ℝ), (∀ x, S'.B.ph x ≤ S'.bregWeight t' x) ∧ M.atlas.Smooth (S'.bregWeight t') ∧ ∀ B p q : ℕ, IsSmoothHerm (MUc Hd S' B p q t') ∧ (MUc Hd S' B p q t').a = (q : ℤ) • muTwDeg Hd B + (p : ℤ) • D.a' ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), Real.log ((MUc Hd S' B p q t').h z) = q * (Real.log (S'.ref.h z) + S'.bregWeight t' (M.proj z) + ∑ r ∈ D.SB B, Real.log (D.vertFactor r z)) + p * Real.log (D.A'.h z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.bregWeight_ge_and_MUc_smooth | exact GlobalTheory.CompanionTheory.Ar.Cusp.bregWeight_ge_and_MUc_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.bregWeight_ge_and_MUc_smooth <;> assumption)
