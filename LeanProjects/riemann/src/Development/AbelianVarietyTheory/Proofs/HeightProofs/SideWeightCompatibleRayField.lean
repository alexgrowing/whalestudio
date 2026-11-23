import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WPtFrame
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CoreFrameCompatibleConstructedPointStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightPsiChoiceTameStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightExportLevelStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PlugPt.sideW_ties : GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (𝒮 : Slots) (ν : NRead hL 𝒮), CoreSlot 𝒮 → ∀ (K : Ctx) (p : WPt 𝒮 K), (sideW ν p).Ties p.O.ex.errX p.O.ex.xd := by
  intro hR hL 𝒮 ν hC K p
  obtain ⟨hRC, hTC, -⟩ := GlobalTheory.Plug.wPt_frame 𝒮 K p
  have ht := GlobalTheory.T.coreFrameCompatible_constructed_point hR 𝒮 hC K p
  obtain ⟨hpsi, hval, htame⟩ := GlobalTheory.T.side_weight_psi_choice_tame hL 𝒮 ν K p
  obtain ⟨hser, hlev, hdat, hsmall⟩ := GlobalTheory.T.side_weight_export_level hR hL 𝒮 ν K p
  refine ⟨?_, ?_, hser, hlev, hdat, hpsi, hval, hsmall, htame⟩
  · show p.x.what₂.r.z.R.C = GlobalTheory.Mem.Col2.TC.cf p.w.I p.w.l p.Z
    rw [hRC, hTC]
  · show Tied p.O.ex.errX p.x.what₂.r.z.core (GlobalTheory.Mem.Col2.TC.cf p.w.I p.w.l p.Z)
    rw [hTC]
    exact ht
