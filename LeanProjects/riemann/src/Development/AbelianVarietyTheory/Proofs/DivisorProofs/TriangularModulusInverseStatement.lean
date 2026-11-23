import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularModulusInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangular_modulus_inverse : ∀ (K : Type) [Field K] (N : ℕ) (R : Subring K) (h b : K) (A : Matrix (Fin N) (Fin N) K) (d : Fin N → K), Small R h → b ∈ R → A.det ≠ 0 → b • A⁻¹ ∈ R.matrix → TriMod R (h * b * b) A d → (∀ i, d i ≠ 0) ∧ TriMod R h A⁻¹ fun i => (d i)⁻¹ := by
  first | exact @GlobalTheory.LatChain.triMod_inv | exact GlobalTheory.LatChain.triMod_inv | (intros; apply GlobalTheory.LatChain.triMod_inv <;> assumption)
