import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartMatrixSmoothInvertible
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_matrix_smooth_invertible : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) (R : AnRead p σ d) (a : ChartForm p σ d), IsKaehlerForm R a → ∀ c : AlgChart p σ d, (∀ i j, ContDiffOn ℝ ∞ (fun v => matIn a c v i j) c.e.target) ∧ (∀ v ∈ c.e.target, IsUnit (matIn a c v).det) ∧ ∀ v ∈ c.e.target, ∀ ξ : ReciprocityTheory.L2DbarEstimates.V d, (a c (c.e.symm v) ξ.ofLp : ℂ) = (ξ.ofLp ᵥ* matIn a c v) ⬝ᵥ star ξ.ofLp := by
  first | exact @GlobalTheory.ChernReg.MatSmooth.matIn_smooth_unit_form | exact GlobalTheory.ChernReg.MatSmooth.matIn_smooth_unit_form | (intros; apply GlobalTheory.ChernReg.MatSmooth.matIn_smooth_unit_form <;> assumption)
