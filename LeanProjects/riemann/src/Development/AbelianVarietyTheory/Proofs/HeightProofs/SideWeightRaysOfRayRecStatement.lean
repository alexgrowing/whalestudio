import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightRaysOfRayRec
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_weight_rays_of_ray_rec : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (𝒮 : Slots) (ν : NRead hL 𝒮) (K : Ctx) (p : WPt 𝒮 K), RayRec (p.w.D p.Z) p.O.ex.nch → (sideW ν p).Rays := by
  first | exact @GlobalTheory.Plug.RaysW.rays_of_rayRec | exact GlobalTheory.Plug.RaysW.rays_of_rayRec | (intros; apply GlobalTheory.Plug.RaysW.rays_of_rayRec <;> assumption)
