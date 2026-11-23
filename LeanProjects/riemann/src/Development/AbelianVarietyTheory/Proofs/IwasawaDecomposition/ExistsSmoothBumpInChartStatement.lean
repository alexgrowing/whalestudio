import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmoothBumpInChart
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenClosureSubset
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_bump_in_chart : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [T2Space (CxPts p σ)] (c : AlgChart p σ d) (C U : Set (CxPts p σ)), IsCompact C → IsOpen U → C ⊆ U → U ⊆ c.e.source → ∃ ρ : CxPts p σ → ℝ, Continuous ρ ∧ ContDiffOn ℝ ∞ (ρ ∘ c.e.symm) c.e.target ∧ (∀ y, 0 ≤ ρ y ∧ ρ y ≤ 1) ∧ (∀ y ∈ C, ρ y = 1) ∧ tsupport ρ ⊆ U := by
  first | exact @GlobalTheory.cutoff_chart | exact GlobalTheory.cutoff_chart | (intros; apply GlobalTheory.cutoff_chart <;> assumption)
