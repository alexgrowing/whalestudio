import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top
namespace GlobalTheory.Fc
structure AllRowsAlt (KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) (N : FamClass → Prop)
    (DR : _root_.GlobalTheory.Fc.R1.DefiniteSideType) : Prop where
  hn4 : Lg1 KP Q Q' fun S => R0.ClassCountBoundAtConstructedPoints S Lk
  jOn : Lg1 KP Q Q' fun S => R0.JInvariantConditionAtConstructedPoints S Lk
  hInstR : Lg1 KP Q Q' fun S => ClassTwoEntries.InstanceRankAtConstructedPoints S Lk
  aC2 : Lg1 KP Q Q' fun S => ClassTwoEntries.DivisionSecondComplementAtConstructedPoints S Lk
  aP10 : Lg1 KP Q Q' fun S => AllBundlePointProperties.LevelPrimeColumnValuationsAtBundlePoints S Lk
  aAtG : Lg1 KP Q Q' fun S => AllBundlePointProperties.ArithmeticConditionAtBundlePoints S Lk
  aPt0 : Lg1 KP Q Q' fun S => PeriodEntriesOverColumns.ReferenceChainEvaluationAtBundlePoints S Lk
  aPtTw : Lg1 KP Q Q' fun S => PeriodEntriesOverColumns.TwistedPointAtBundlePoints S Lk
  aPer0 : Lg1 KP Q Q' fun S => PeriodEntriesOverColumns.PeriodAtZeroAtBundlePoints S Lk
  aPerTw : Lg1 KP Q Q' fun S => PeriodEntriesOverColumns.TwistedPeriodAtBundlePoints S Lk
  tie : Lg1 KP Q Q' fun S => PeriodEntriesOverColumns.Row_tie S Lk
  hRB : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotRowBoundCondition S Lk
  hTw : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotTwistCondition S Lk
  hPA : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition S Lk
  hLamP : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotLambdaPrimeCondition S Lk
  hDivG : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotDivisorCondition S Lk
  hDcPtG : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotDecompositionPointCondition S Lk
  selJ : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotSelectionJumpCondition S Lk
  sLp : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotLpCondition S Lk
  sO : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotOrderCondition S Lk
  hServ : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotServiceCondition S Lk
  zL : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotZeroLocusCondition S Lk
  hTF : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotTorsionFreeCondition S Lk
  c30 : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.CountsIrreducibilityConstants' S Lk
  rRows : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotDefiniteRowsCondition DR S Lk
  nRest : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotNormCondition S Lk N
end GlobalTheory.Fc
end
end
