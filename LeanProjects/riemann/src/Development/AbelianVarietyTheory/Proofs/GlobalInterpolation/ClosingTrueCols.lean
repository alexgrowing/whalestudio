import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EFirstGeOfULastNonpos
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueColumnsRowSharpBoundsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LvT.Built.TrueCols

theorem closing_true_cols : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ColIn.JetsIn I → GlobalTheory.LvT.WtSign.BaseSigns B → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (u : (I.rec7 l Z).what₂.Word), Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (I.rec7 l Z) u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT Y (I.tw l l0 Z) u := by
  intro B X I hOk hJ hS l Z l0 Y u
  exact GlobalTheory.T.trueColumns_row_sharp_bounds B X I hOk hJ hS l l0 Z Y u
end GlobalTheory.LvT.Built.TrueCols
