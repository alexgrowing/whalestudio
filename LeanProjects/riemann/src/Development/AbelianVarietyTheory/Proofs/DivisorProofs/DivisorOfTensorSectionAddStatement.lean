import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorOfTensorSectionAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_of_tensor_section_add : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k) (M M' : HermLB q), (∀ E E' : CartierDiv X, Can M E → Can M' E' → Can (M.tens M') (E + E') ∧ Can M.dual (-E)) ∧ ∀ (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r) (r' : M'.B.ι → X.functionFieldˣ) (hr' : IsRatSec M'.B r'), ∃ (s : (M.tens M').B.ι → X.functionFieldˣ) (hs : IsRatSec (M.tens M').B s), (M.tens M').div hs = M.div hr + M'.div hr' := by
  first | exact @GlobalTheory.LatChain.CanTens.can_tens_dual | exact GlobalTheory.LatChain.CanTens.can_tens_dual | (intros; apply GlobalTheory.LatChain.CanTens.can_tens_dual <;> assumption)
