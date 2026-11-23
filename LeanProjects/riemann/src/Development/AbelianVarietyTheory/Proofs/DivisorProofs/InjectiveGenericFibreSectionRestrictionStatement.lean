import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveGenericFibreSectionRestriction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdaptedMinorNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUnipotentTriangularizingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRegularAdaptedLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityCriterionNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPlaceOfNeZeroMaximalStatement
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_generic_fibre_section_restriction : ∀ {F : Type} [Field F] [NumberField F] {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {s : W ⟶ Sp F} {jB : W ⟶ X} {d : ℕ},
    IsArithVar q d → IsPullback jB s q (spMap (algebraMap (𝓞 F) F)) → ∀ (V : X.Opens), IsAffineOpen V →
    Function.Injective (jB.app V) := by
  first | exact @GlobalTheory.GenericFibreInj.app_injective | exact GlobalTheory.GenericFibreInj.app_injective | (intros; apply GlobalTheory.GenericFibreInj.app_injective <;> assumption)
