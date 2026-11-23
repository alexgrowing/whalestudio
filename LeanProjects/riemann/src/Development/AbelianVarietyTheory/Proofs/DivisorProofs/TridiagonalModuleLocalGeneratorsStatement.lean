import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TridiagonalModuleLocalGenerators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tridiagonal_module_local_generators : ∀ (K : Type) [Field K] (N : ℕ) (R : Subring K) (γ b : K) (A : Matrix (Fin N) (Fin N) K) (d y : Fin N → K), γ ∈ R → b ∈ R → A ∈ R.matrix → (∀ l, y l ∈ R) → TriMod R (γ * b) A d → (∀ i : Fin N, d i ∈ R ∧ Lc R (gens γ y i.succ) ((A.mulVec y) i - d i * y i)) ∧ ∀ i s, Lc R (gens γ y i) (gens γ (A.mulVec y) i s) := by
  first | exact @GlobalTheory.LatChain.lc_gens_of_triMod | exact GlobalTheory.LatChain.lc_gens_of_triMod | (intros; apply GlobalTheory.LatChain.lc_gens_of_triMod <;> assumption)
