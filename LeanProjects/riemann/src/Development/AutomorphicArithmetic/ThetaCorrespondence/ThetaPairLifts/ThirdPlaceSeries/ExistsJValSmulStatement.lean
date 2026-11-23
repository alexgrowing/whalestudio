import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurScalarLemmaStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsOfVal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsJValSmul

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_gram_family_property_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} {l : I.Laws} {Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), Formalism.L2.Forms.gramP (I.rec7 l Z) = 1 → ∀ (u : B.Word) (cv : GlobalTheory.TopVal.Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W), _root_.GlobalTheory.TopVal.ValEqvAlt W cv → cv ≠ 0 → ∀ j₀, GlobalTheory.Core.Rk.Top.IsJ u (_root_.GlobalTheory.Fam.pk_z W).MX j₀ → ∃ a : ℂ, a ≠ 0 ∧ _root_.GlobalTheory.TopVal.ValuationCompatible W cv (a • j₀) := by
  first | exact @_root_.GlobalTheory.TopVal.exists_jVal_smul_alt | exact _root_.GlobalTheory.TopVal.exists_jVal_smul_alt | (intros; apply _root_.GlobalTheory.TopVal.exists_jVal_smul_alt <;> assumption)
end
