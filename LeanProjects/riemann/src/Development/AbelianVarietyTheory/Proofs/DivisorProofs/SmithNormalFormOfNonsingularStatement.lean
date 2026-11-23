import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmithNormalFormOfNonsingular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smith_normal_form_of_nonsingular : ∀ (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (N : ℕ) (A : Matrix (Fin N) (Fin N) R), A.det ≠ 0 → ∃ (u v u' v' : Matrix (Fin N) (Fin N) R) (g : Fin N → R), u * v = 1 ∧ u' * v' = 1 ∧ A = u * Matrix.diagonal g * u' := by
  first | exact @GlobalTheory.LatChain.smith_of_det_ne_zero | exact GlobalTheory.LatChain.smith_of_det_ne_zero | (intros; apply GlobalTheory.LatChain.smith_of_det_ne_zero <;> assumption)
