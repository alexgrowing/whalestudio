import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightCompatibleRayField
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideWChrStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideWExportSmallStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem GlobalTheory.PlugPt.side_weight_ties_of_ray_field : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮), CoreSlot 𝒮 → ∀ (K : Ctx) (p : WPt 𝒮 K), (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).Ties p.O.ex.errX p.O.ex.xd := by
  intro hR hL 𝒮 ν hC K p
  obtain ⟨hRC, hTC, -⟩ := GlobalTheory.Plug.wPt_frame 𝒮 K p
  have ht := GlobalTheory.T.coreFrameCompatible_constructed_point hR 𝒮 hC K p
  obtain ⟨hpsi, hval, htame⟩ := _root_.GlobalTheory.T.side_weight_psi_choice_tame_tie hL 𝒮 ν K p
  obtain ⟨hser, hlev, hdat, hsmall⟩ := _root_.GlobalTheory.T.side_weight_export_all_data_small_has hR hL 𝒮 ν K p
  refine ⟨?_, ?_, hser, hlev, hdat, hpsi, hval, hsmall, htame⟩
  · show p.x.what₂.r.z.R.C = GlobalTheory.Mem.Col2.TC.cf p.w.I p.w.l p.Z
    rw [hRC, hTC]
  · show Tied p.O.ex.errX p.x.what₂.r.z.core (GlobalTheory.Mem.Col2.TC.cf p.w.I p.w.l p.Z)
    rw [hTC]
    exact ht
end
