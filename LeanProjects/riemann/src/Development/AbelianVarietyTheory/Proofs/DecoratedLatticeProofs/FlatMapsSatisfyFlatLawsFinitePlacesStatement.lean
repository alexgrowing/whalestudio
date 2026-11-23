import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces : ∀ D : D7, GlobalTheory.FinPl.FlatLaws D := by
  first | exact @GlobalTheory.FinPl.flatLaws_all | exact GlobalTheory.FinPl.flatLaws_all | (intros; apply GlobalTheory.FinPl.flatLaws_all <;> assumption)
