import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetEvaluationPowerSeries
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RosLevel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.RayEv.Transport
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_evaluation_power_series : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (R : Type) [CommRing R] (I : Ideal R), I.FG → ∀ f : R →+* C, (∀ r, ‖f r‖ ≤ 1) → (∀ r ∈ I, ‖f r‖ < 1) → ∀ (W : Type) [CommRing W] [Algebra R W] [Module.Finite R W] (ρ : Type) [Fintype ρ] [DecidableEq ρ] (m : ℕ) (κ : W →+* Jet C ρ m), (∀ r, κ (algebraMap R W r) = algebraMap C (Jet C ρ m) (f r)) → ∀ (X : Type) (s : W) (t : X → W), (∀ e : ℕ, ∃ S : Finset X, (∀ α ∉ S, t α ∈ I.map (algebraMap R W) ^ (e + 1)) ∧ s - ∑ α ∈ S, t α ∈ I.map (algebraMap R W) ^ (e + 1)) → ∀ (u : Jet C ρ m) (g : X → MvPowerSeries ρ C), (∀ α, psJet m (g α) = u * κ (t α)) → (∀ n : ρ →₀ ℕ, (n.sum fun _ k => k) ≤ m → Summable fun α => MvPowerSeries.coeff n (g α)) ∧ ∀ g₀ : MvPowerSeries ρ C, (∀ n : ρ →₀ ℕ, (n.sum fun _ k => k) ≤ m → HasSum (fun α => MvPowerSeries.coeff n (g α)) (MvPowerSeries.coeff n g₀)) → psJet m g₀ = u * κ s := by
  first | exact @GlobalTheory.AdicConverge.converge | exact GlobalTheory.AdicConverge.converge | (intros; apply GlobalTheory.AdicConverge.converge <;> assumption)
