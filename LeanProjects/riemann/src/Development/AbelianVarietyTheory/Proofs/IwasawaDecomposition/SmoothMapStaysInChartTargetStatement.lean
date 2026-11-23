import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothMapStaysInChartTarget
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocMapOfMem
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_map_stays_in_chart_target : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) (R : AnRead p σ d) (a : ChartForm p σ d), IsKaehlerForm R a → ∀ (c c₀ : AlgChart p σ d) (f : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d) (W : Set (CxPts p σ)) (ε : ℝ), ContDiff ℝ ∞ f → W ⊆ c.e.source → (∀ y ∈ W, ∀ η : ReciprocityTheory.L2DbarEstimates.V d, a c y η.ofLp < ε → f (c.e y, η) ∈ c.e.target) → ∀ v ∈ c₀.e.target, c₀.e.symm v ∈ W → ∀ ξ : ReciprocityTheory.L2DbarEstimates.V d, a c₀ (c₀.e.symm v) ξ.ofLp < ε → ∃ Φ : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d, ContDiffAt ℝ ∞ Φ (v, ξ) ∧ Φ (v, ξ) ∈ c.e.target ∧ (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => GlobalTheory.ChernReg.ExphLoc.locMap c f c₀ (c₀.e.symm q.1) q.2.ofLp) =ᶠ[𝓝 (v, ξ)] fun q => c.e.symm (Φ q) := by
  first | exact @GlobalTheory.ChernReg.ExphLoc.locMap_eventuallyEq_symm | exact GlobalTheory.ChernReg.ExphLoc.locMap_eventuallyEq_symm | (intros; apply GlobalTheory.ChernReg.ExphLoc.locMap_eventuallyEq_symm <;> assumption)
