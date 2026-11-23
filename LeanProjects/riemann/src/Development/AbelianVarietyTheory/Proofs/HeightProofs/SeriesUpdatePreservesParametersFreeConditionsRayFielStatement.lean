import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SeriesUpdatePreservesParamFreeConditionsRayField
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seriesUpdate_preserves_parameterFreeConditions_rayFields : ∀ (D : D7) (nch : NChoice D) (s : Side D nch) (EX : ErrX D) (xd : ThData D) kap lam err, (s.Ties EX xd → (s.upd kap lam err).Ties EX xd) ∧ (s.Rays → (s.upd kap lam err).Rays) := by
  first | exact @GlobalTheory.PlugPt.side_upd_ties_rays | exact GlobalTheory.PlugPt.side_upd_ties_rays | (intros; apply GlobalTheory.PlugPt.side_upd_ties_rays <;> assumption)
