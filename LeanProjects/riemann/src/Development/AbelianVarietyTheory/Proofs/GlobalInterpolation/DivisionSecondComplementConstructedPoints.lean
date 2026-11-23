import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivisionSecondComplementAtConstructedPoints
import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleConstantsClosedUnderSizeBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.ClassTwoEntries

theorem divisionSecondComplement_constructedPoints : ∀ (Bd : BdT) (Q : V4.Slot) (Lk : LkT Bd), ClassTwoEntries.DivisionSecondComplementAtConstructedPoints Q Lk := by
  intro Bd Q Lk
  exact Row0.row (Row0.of_all (Q := Q) fun 𝒜 =>
    GlobalTheory.admissibleConstants_closed_under_sizeBounds (W3 𝒜) fun _ h => ⟨h.2.2.1, h.2.2.2⟩) Lk

end GlobalTheory.Fc.ClassTwoEntries
