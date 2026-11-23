import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnSidePropertiesTrueColumnsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardKernelDataWithStandardReadersStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientFieldConditionOfStandardKernelCompariStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueChainComplexFormsStabiliserLawStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueChainStabilisersEqStandardReaderPointsStatement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Pdv.duty_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → I.StdKer l Z t → GlobalTheory.Pdv.IsEntC t → GlobalTheory.Pdv.Duty t := by
  intro B X I hOk hP l Z l0 L hT Gi Gl K Y cX ex t hN hJ htw hS hE
  obtain ⟨t', hS', hR', -⟩ := GlobalTheory.T.standardKernelData_with_standardBaseLevels I hOk hP l Z L hT Gi Gl K Y cX ex t hS
  refine ⟨GlobalTheory.T.columnSide_properties_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t hN hS, hE, GlobalTheory.T.coefficientFieldCondition_of_standardKernelComparison I hOk hP l Z L hT Gi Gl K Y cX ex t hJ hS,
    ⟨t', GlobalTheory.T.columnSide_properties_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t' hN hS', ?_⟩⟩
  intro u μ _
  refine ⟨GlobalTheory.Pdv.stabStd I l Z u μ, ?_, GlobalTheory.T.trueChain_stabilizers_eq_standardBaseLevel_points I hOk hP l Z L hT Gi Gl K Y cX ex t' hN hS' hR' u μ⟩
  rw [htw]
  exact GlobalTheory.T.trueChain_complexForms_stabiliser_law I hOk hP l Z l0 Y.Qp t'.O hS'.O u μ
