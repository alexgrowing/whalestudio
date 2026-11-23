import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicThetaSeriesComparisonIndepScalarsErrorsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

set_option maxHeartbeats 1000000 in

theorem side_upd_ties_rays : ∀ (D : D7) (nch : NChoice D) (s : Side D nch) (EX : ErrX D) (xd : ThData D) kap lam err,
    (s.Ties EX xd → (s.upd kap lam err).Ties EX xd) ∧ (s.Rays → (s.upd kap lam err).Rays) := by
  intro D nch s EX xd kap lam err
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact
      { frame := h.frame
        tied := h.tied
        series := GlobalTheory.T.adelicThetaSeriesComparison_indep_scalars_errors D nch s kap lam err h.series
        level := h.level
        data := h.data
        psi := h.psi
        psiVal := h.psiVal
        small := h.small
        types := h.types }
  · exact h

end GlobalTheory.PlugPt
