import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ReferenceChainEvaluationAtBundlePoints
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PropertyAtConstructedPointsOfTrueColumnsViewStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedPointRowAdmissibleTrueColumnsStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.PeriodEntriesOverColumns

theorem row_aPtTw_of_overCols : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), PeriodEntriesOverColumns.TwistedPointAtBundlePoints Q Lk := by
  intro Q hQ Bd Lk
  have h0 : Row0 Q (EvC fun D O => Formalism.L2.G.Adm2InU.TwistedPointIntegral D O.ex.tw) := by
    apply validForConstructedPointClasses_eventuallyWorkingClass
    refine EvP.of_all fun _ K _ β hβ => ?_
    have hc : β.Is HasCols := hQ K β.X β.f β.T β.c hβ
    refine GlobalTheory.T.property_at_constructedPoints_of_trueColumnsView (fun D O => Formalism.L2.G.Adm2InU.TwistedPointIntegral D O.ex.tw) ?_ K β hc
    intro B f T w Z O nch hv _ _
    rw [hv.tw_eq]
    exact GlobalTheory.T.twistedPointRow_admissible_trueColumns w.I w.ok w.l Z w.l0
  exact h0.row Lk

end GlobalTheory.Fc.PeriodEntriesOverColumns
