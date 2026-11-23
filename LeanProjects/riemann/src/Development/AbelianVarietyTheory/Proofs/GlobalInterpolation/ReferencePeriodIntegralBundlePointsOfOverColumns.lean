import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ReferenceChainEvaluationAtBundlePoints
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodAdmissibleOfIntegralPeriodRowsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PropertyAtConstructedPointsOfTrueColumnsViewStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Fc.PeriodEntriesOverColumns.row_aPer0_of_overCols :
    ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), PeriodEntriesOverColumns.PeriodAtZeroAtBundlePoints Q Lk := by
  intro Q hQ Bd Lk
  have h : Row0 Q (EvC fun D _ => Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl D) :=
    validForConstructedPointClasses_eventuallyWorkingClass (EvP.of_all fun _ K _ β hq =>
      GlobalTheory.T.property_at_constructedPoints_of_trueColumnsView (fun D _ => Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl D)
        (fun _ _ _ w Z _ _ hv _ _ => GlobalTheory.T.periodClassSumWeyl_of_rowInt w.I w.ok w.pins w.l Z hv.rowInt) K β (hQ _ _ _ _ _ hq))
  exact h.row Lk
