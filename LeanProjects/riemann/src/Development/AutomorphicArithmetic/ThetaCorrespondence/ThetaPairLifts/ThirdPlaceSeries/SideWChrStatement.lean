import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightPsiChoiceTameStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideWChr
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_weight_psi_choice_tame_tie : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (K : Ctx) (p : WPt 𝒮 K), Formalism.L2.Host.PsiChoiceCompatible (p.w.D p.Z) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cf p.O.ex.nch (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).tp ∧ (∀ v, (p.w.D p.Z).what₂.muAt v ≠ (p.w.D p.Z).what₂.mu0 → ((_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).tp.psi v).ValuesIn 0 (p.w.D p.Z).what₂.embLL) ∧ GlobalTheory.DimPartsCompare.TameTie (p.w.D p.Z) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cf.W.om := by
  first | exact @_root_.GlobalTheory.PlugPt.side_weight_psi_values_tame_tie | exact _root_.GlobalTheory.PlugPt.side_weight_psi_values_tame_tie | (intros; apply _root_.GlobalTheory.PlugPt.side_weight_psi_values_tame_tie <;> assumption)
end
