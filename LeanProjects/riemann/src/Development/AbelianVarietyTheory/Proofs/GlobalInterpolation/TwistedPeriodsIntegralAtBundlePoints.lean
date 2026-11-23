import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ReferenceChainEvaluationAtBundlePoints
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodTwistOfIntegralRowsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PropertyAtConstructedPointsOfTrueColumnsViewStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.PeriodEntriesOverColumns

theorem row_aPerTw_of_overCols : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), PeriodEntriesOverColumns.TwistedPeriodAtBundlePoints Q Lk := by
  intro Q hQ Bd Lk
  refine Row0.row (Q := Q) (H := H_aPerTw) ?_ Lk
  refine validForConstructedPointClasses_eventuallyWorkingClass (R := fun D O => Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible D O.X O.ex.tw) (EvP.of_all fun _ K _ β hβ => ?_)
  refine GlobalTheory.T.property_at_constructedPoints_of_trueColumnsView (fun D O => Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible D O.X O.ex.tw) ?_ K β (hQ _ _ _ _ _ hβ)
  intro B f T w Z O nch cv _ _
  obtain ⟨tp, htp⟩ := cv.tup
  rw [cv.tw_eq]
  exact GlobalTheory.T.admissible_period_twist_of_integral_rows w.I w.ok w.pins w.l Z w.l0 cv.rowInt nch tp htp O.X

end GlobalTheory.Fc.PeriodEntriesOverColumns
