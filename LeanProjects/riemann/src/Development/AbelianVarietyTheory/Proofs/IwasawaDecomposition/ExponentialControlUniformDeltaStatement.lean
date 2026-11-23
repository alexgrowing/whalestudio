import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialControlUniformDelta
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenClosureSubset
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_control_uniform_delta : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) (R : AnRead p σ d) (a : ChartForm p σ d), IsKaehlerForm R a → ∀ (E : ChartMap p σ d) (W : Set (CxPts p σ)) (ε : ℝ), 0 < ε → ExphOn.IsExphOn a E W ε → ∀ (c : AlgChart p σ d) (L : Set (CxPts p σ)) (r : ℝ), IsCompact L → L ⊆ W → L ⊆ c.e.source → 0 < r → ∃ δ > 0, ∀ c₀ : AlgChart p σ d, ∀ y ∈ L, y ∈ c₀.e.source → ∀ ξ, a c₀ y ξ < δ → E c₀ y ξ ∈ c.e.source ∧ c.e (E c₀ y ξ) ∈ Metric.ball (c.e y) r := by
  first | exact @GlobalTheory.ChernReg.ExphOn.short_vectors_near_base | exact GlobalTheory.ChernReg.ExphOn.short_vectors_near_base | (intros; apply GlobalTheory.ChernReg.ExphOn.short_vectors_near_base <;> assumption)
