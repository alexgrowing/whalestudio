import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightCompatibleRayFieldStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideWTies
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_weight_ties_err_of_ray_field_core_slot : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮), CoreSlot 𝒮 → ∀ (K : Ctx) (p : WPt 𝒮 K), (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).Ties p.O.ex.errX p.O.ex.xd := by
  first | exact @_root_.GlobalTheory.PlugPt.side_weight_ties_of_ray_field | exact _root_.GlobalTheory.PlugPt.side_weight_ties_of_ray_field | (intros; apply _root_.GlobalTheory.PlugPt.side_weight_ties_of_ray_field <;> assumption)
end
