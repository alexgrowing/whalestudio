import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisIntegerAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_basis_integer_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X) (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)), GlobalTheory.LineNorm.IsTanBasis t x e → ∃ ρ : 𝓞 E →+* Matrix (Fin g) (Fin g) R, ∀ (K : Type) [CommRing K] (ψ : R →+* K) (a : 𝓞 E) (cf : Fin g → K) (w : Sp (DualNumber K) ⟶ t.G.left), IsCombAtG t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ e i) cf w → IsCombAtG t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ e i) (((ρ a).map ψ).mulVec cf) (w ≫ (t.act.act a).left) := by
  first | exact @GlobalTheory.TanActMat.exists_actMatrix_bc | exact GlobalTheory.TanActMat.exists_actMatrix_bc | (intros; apply GlobalTheory.TanActMat.exists_actMatrix_bc <;> assumption)
