import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVerticalCartierDivisorOfEquations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vertical_cartier_divisor_of_equations : ∀ (X : Scheme.{0}) [IsIntegral X] (p : ℕ) (η : X → X.functionFieldˣ), VEq p η → ∃ E : CartierDiv X, Vert p E ∧ ∀ x, Ov p x → E.IsEqn x (η x) := by
  first | exact @GlobalTheory.LatChain.exists_vert_isEqn | exact GlobalTheory.LatChain.exists_vert_isEqn | (intros; apply GlobalTheory.LatChain.exists_vert_isEqn <;> assumption)
