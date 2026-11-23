import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivisionSecondComplementAtConstructedPoints
import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeSignatureIndepAndClassNumberItemsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory

theorem row_hInstR_of_hU (hU : ∀ D : D7, MassRatioUnderVolume D) : ∀ (Bd : BdT) (Q : V4.Slot) (Lk : LkT Bd), ClassTwoEntries.InstanceRankAtConstructedPoints Q Lk :=
  fun _ Q Lk => Row0.row (Row0.of_all (Q := Q) fun _ => by
    intro eps Fm _ x _ i
    exact GlobalTheory.T.volume_signature_indep_and_classNumberItems hU (Fm.D x i)) Lk

end GlobalTheory
