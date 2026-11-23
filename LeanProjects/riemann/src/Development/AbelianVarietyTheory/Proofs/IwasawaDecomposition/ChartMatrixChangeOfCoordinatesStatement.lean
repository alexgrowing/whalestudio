import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartMatrixChangeOfCoordinates
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_matrix_change_of_coordinates : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) (R : AnRead p σ d) (a : ChartForm p σ d), IsKaehlerForm R a → ∀ c c' : AlgChart p σ d, ∀ v ∈ c.e.target, c.e.symm v ∈ c'.e.source → ∀ ξ ζ : ReciprocityTheory.L2DbarEstimates.V d, (ξ.ofLp ᵥ* matIn a c v) ⬝ᵥ star ζ.ofLp = ((fderiv ℂ (c'.e ∘ c.e.symm) v ξ).ofLp ᵥ* matIn a c' ((c'.e ∘ c.e.symm) v)) ⬝ᵥ star (fderiv ℂ (c'.e ∘ c.e.symm) v ζ).ofLp := by
  first | exact @GlobalTheory.ChernReg.MatCompat.matIn_trans | exact GlobalTheory.ChernReg.MatCompat.matIn_trans | (intros; apply GlobalTheory.ChernReg.MatCompat.matIn_trans <;> assumption)
