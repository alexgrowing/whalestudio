import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WPtFrame
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmallFrameAtColumnStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem sideW_export_small : GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (𝒮 : Slots) (ν : NRead hL 𝒮) (K : Ctx) (p : WPt 𝒮 K), Nonempty (GlobalTheory.SeriesTie.ExportTie (sideW ν p).YS (sideW ν p).v₀) ∧ LevelIs (p.w.D p.Z).nexp ((sideW ν p).R.eG.trans (sideW ν p).cG) (sideW ν p).P0 (sideW ν p).ψ0⁻¹ ∧ AllData (p.w.D p.Z).nexp p.O.ex.xd.xd0 ∧ SmallHas (p.w.D p.Z) (sideW ν p).cf := by
  intro hR hL 𝒮 ν K p
  have hE : (sideW ν p).Export p.O.ex.xd := (ν.rd _ _ _ _ _ _ _ _ _ _ _ _ p.x.nx).2.1.down
  have hcf : (sideW ν p).cf = Fr.at (p.w.st p.Z) p.f := (GlobalTheory.Plug.wPt_frame 𝒮 K p).2.1
  refine ⟨hE.1, hE.2.1, hE.2.2, ?_⟩
  rw [hcf]
  exact GlobalTheory.T.small_frame_at_column hR p.B p.f p.T p.w p.Z

end GlobalTheory
