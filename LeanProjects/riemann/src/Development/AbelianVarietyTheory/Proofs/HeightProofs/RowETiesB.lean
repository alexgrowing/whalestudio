import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RayClassFieldsInCoefficientFieldConstructedPointStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightRaysOfRayRecStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightCompatibleRayFieldStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SeriesUpdatePreservesParametersFreeConditionsRayFielStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

theorem rowE_tiesB : GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (𝒮 : Slots) (ν : NRead hL 𝒮) (Q : V4.Slot),
    CoreSlot 𝒮 → RowE (sAnd Q RayPosition) (linkOf (pinPt ν)) fun _ => TiesB := by
  intro hR hL 𝒮 ν Q hC
  refine RowE.of_all ?_
  intro κ K β c b _ hq hl
  have hray : RayRec β.D β.O.ex.nch := GlobalTheory.T.rayClassFieldsInCoefficientField_constructedPoint K β hq.2
  obtain ⟨p, b', ⟨kap, lam, err, hs⟩, heq⟩ := hl
  let F : (Σ (D : D7) (O : Obj D), BdPt D O c) → Prop := fun x => RayRec x.1 x.2.1.ex.nch → TiesB x.1 x.2.1 c x.2.2
  have hp : F ⟨p.w.D p.Z, p.O, b'⟩ := by
    intro hr
    have hu := GlobalTheory.T.seriesUpdate_preserves_parameterFreeConditions_rayFields _ _ (sideW ν p) p.O.ex.errX p.O.ex.xd kap lam err
    show (sidePt b').Ties p.O.ex.errX p.O.ex.xd ∧ (sidePt b').Rays
    rw [hs]
    exact ⟨hu.1 (GlobalTheory.T.side_weight_compatible_ray_field hR hL 𝒮 ν hC K p), hu.2 (GlobalTheory.T.side_weight_rays_of_ray_rec hL 𝒮 ν K p hr)⟩
  have hb : F ⟨β.D, β.O, b⟩ := (congrArg F heq).mpr hp
  exact hb hray

end GlobalTheory.PlugPt
