import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ClassCountBoundAtConstructedPoints
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivisionSecondComplementAtConstructedPoints
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelPrimeColumnValuationsAtBundlePoints
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ReferenceChainEvaluationAtBundlePoints
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top

namespace GlobalTheory.Fc

def Lg1 (KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (r : V4.Slot → Prop) : Prop :=
  ∃ R : V4.Slot, LargeBaseCondition KP Q R ∧ r (sAnd Q' R)

structure AllRows (KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Lk : LkT Bundle) (N : FamClass → Prop)
    (DR : R1.DefT) : Prop where
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
  hRB : Lg1 KP Q Q' fun S => R1.RankBoundAtBundlePoints S Lk
  hTw : Lg1 KP Q Q' fun S => R1.TwistConditionAtBundlePoints S Lk
  hPA : Lg1 KP Q Q' fun S => R1.PeriodAdmissibilityAtBundlePoints S Lk
  hLamP : Lg1 KP Q Q' fun S => R1.LambdaPositivityAtBundlePoints S Lk
  hDivG : Lg1 KP Q Q' fun S => R1.DivisorConditionAtBundlePoints S Lk
  hDcPtG : Lg1 KP Q Q' fun S => R1.DecompositionConditionAtBundlePoints S Lk
  selJ : Lg1 KP Q Q' fun S => R1.JSelectionAtBundlePoints S Lk
  sLp : Lg1 KP Q Q' fun S => R1.LpSelectionAtBundlePoints S Lk
  sO : Lg1 KP Q Q' fun S => R1.IntegralSelectionAtBundlePoints S Lk
  hServ : Lg1 KP Q Q' fun S => R1.SerreConditionAtBundlePoints S Lk
  zL : Lg1 KP Q Q' fun S => R1.LZeroConditionAtBundlePoints S Lk
  hTF : Lg1 KP Q Q' fun S => R1.TorsionFreenessAtBundlePoints S Lk
  c30 : Lg1 KP Q Q' fun S => R1.CountsIrreducibilityConstants S Lk
  rRows : Lg1 KP Q Q' fun S => R1.RestRowsConditionAtBundlePoints DR S Lk
  nRest : Lg1 KP Q Q' fun S => R1.PredicateAtBundlePoints S Lk N

end GlobalTheory.Fc

end
