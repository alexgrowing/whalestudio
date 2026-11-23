import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowCountsOfLinkedTies
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.CountRowByName

theorem row_counts_of_labels : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Lk : LkT Bundle), (Lg1 KP Q Q' fun S => RL.LabelCondition S Lk) → Lg1 KP Q Q' fun S => R1.CountsIrreducibilityConstants S Lk :=
  fun hSW _ _ _ Lk ⟨R, hR, h⟩ => ⟨R, hR, GlobalTheory.CountRow.row_counts_of_ties hSW _ Lk h⟩

end GlobalTheory.CountRowByName
