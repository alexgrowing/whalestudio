import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialControlGlueRight
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenClosureSubset
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_control_glue_right : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) (a : ChartForm p σ d) (c : AlgChart p σ d) (E E' : ChartMap p σ d) (ρ : CxPts p σ → ℝ) (W W' W₀ O₁ : Set (CxPts p σ)) (ε ε' ε'' r : ℝ), ExphOn.IsExphOn a E W ε → ExphOn.IsExphOn a E' W' ε' → IsOpen W₀ → IsOpen O₁ → W₀ ⊆ W → O₁ ⊆ W' → Continuous ρ → (∀ y, 0 ≤ ρ y ∧ ρ y ≤ 1) → (∀ y ∈ O₁, ρ y = 1) → tsupport ρ ⊆ W' → W' ⊆ c.e.source → ε'' ≤ ε → ε'' ≤ ε' → (∀ y ∈ W₀ ∩ tsupport ρ, Metric.ball (c.e y) r ⊆ c.e.target) → (∀ c₀ : AlgChart p σ d, ∀ y ∈ W₀ ∩ tsupport ρ, y ∈ c₀.e.source → ∀ ξ, a c₀ y ξ < ε'' → E c₀ y ξ ∈ c.e.source ∧ c.e (E c₀ y ξ) ∈ Metric.ball (c.e y) r) → (∀ c₀ : AlgChart p σ d, ∀ y ∈ tsupport ρ, y ∈ c₀.e.source → ∀ ξ, a c₀ y ξ < ε'' → E' c₀ y ξ ∈ c.e.source ∧ c.e (E' c₀ y ξ) ∈ Metric.ball (c.e y) r) → ContDiffOn ℝ ∞ (ρ ∘ c.e.symm) c.e.target → ∀ c₀ c' : AlgChart p σ d, ∀ v ∈ c₀.e.target, c₀.e.symm v ∈ W₀ ∪ O₁ → ∀ ξ : ReciprocityTheory.L2DbarEstimates.V d, a c₀ (c₀.e.symm v) ξ.ofLp < ε'' → ExphOn.glue c ρ E E' c₀ (c₀.e.symm v) ξ.ofLp ∈ c'.e.source → ContDiffAt ℝ ∞ (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => c'.e (ExphOn.glue c ρ E E' c₀ (c₀.e.symm q.1) q.2.ofLp)) (v, ξ) := by
  first | exact @GlobalTheory.ChernReg.ExphOn.glue_smooth | exact GlobalTheory.ChernReg.ExphOn.glue_smooth | (intros; apply GlobalTheory.ChernReg.ExphOn.glue_smooth <;> assumption)
