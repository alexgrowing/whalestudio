import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularFrameDiagonalRatios
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangular_frame_diagonal_ratios : ∀ (K : Type) [Field K] (N : ℕ) (R : Subring K) (M : Matrix (Fin N) (Fin N) K) (j : Fin N) (γ : K) (η : Fin (N + 1) → K), Fr R M → γ ∈ R → γ ≠ 0 → (∀ i, Gen R (gens γ (fun l => M⁻¹ l j) i) (η i)) → (∃ B : Matrix (Fin N) (Fin N) K, B.BlockTriangular id ∧ Fr R (dg j γ * M * B) ∧ ∀ i, B i i = η i.castSucc / η i.succ) ∧ (η 0)⁻¹ ∈ R ∧ η (Fin.last N) / γ ∈ R ∧ (∀ i, η i ∈ R ∧ γ / η i ∈ R) ∧ ∀ i : Fin N, η i.succ / η i.castSucc ∈ R ∧ ∃ α ∈ R, ∃ β ∈ R, η i.castSucc = α * M⁻¹ i j + β * η i.succ := by
  first | exact @GlobalTheory.LatChain.frame_of_content_gens | exact GlobalTheory.LatChain.frame_of_content_gens | (intros; apply GlobalTheory.LatChain.frame_of_content_gens <;> assumption)
