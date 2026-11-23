import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularModulusProducts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangular_modulus_products : ∀ (K : Type) [Field K] (N : ℕ) (R : Subring K) (h b : K) (A A' : Matrix (Fin N) (Fin N) K) (d d' : Fin N → K), h ∈ R → b ∈ R → (b • A ∈ R.matrix → b • A' ∈ R.matrix → TriMod R (h * b) A d → TriMod R (h * b) A' d' → TriMod R h (A * A') fun i => d i * d' i) ∧ ∀ B B' : Matrix (Fin N) (Fin N) K, B.BlockTriangular id → B'.BlockTriangular id → B ∈ R.matrix → b • B' ∈ R.matrix → TriMod R (h * b) A d → TriMod R h (B * A * B') fun i => B i i * d i * B' i i := by
  first | exact @GlobalTheory.LatChain.triMod_mul_triMod | exact GlobalTheory.LatChain.triMod_mul_triMod | (intros; apply GlobalTheory.LatChain.triMod_mul_triMod <;> assumption)
