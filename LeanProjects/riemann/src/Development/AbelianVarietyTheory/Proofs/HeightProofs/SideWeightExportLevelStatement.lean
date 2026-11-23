import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightExportLevel
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_weight_export_level : GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (𝒮 : Slots) (ν : NRead hL 𝒮) (K : Ctx) (p : WPt 𝒮 K), Nonempty (GlobalTheory.SeriesTie.ExportTie (sideW ν p).YS (sideW ν p).v₀) ∧ LevelIs (p.w.D p.Z).nexp ((sideW ν p).R.eG.trans (sideW ν p).cG) (sideW ν p).P0 (sideW ν p).ψ0⁻¹ ∧ AllData (p.w.D p.Z).nexp p.O.ex.xd.xd0 ∧ SmallHas (p.w.D p.Z) (sideW ν p).cf := by
  first | exact @GlobalTheory.sideW_export_small | exact GlobalTheory.sideW_export_small | (intros; apply GlobalTheory.sideW_export_small <;> assumption)
