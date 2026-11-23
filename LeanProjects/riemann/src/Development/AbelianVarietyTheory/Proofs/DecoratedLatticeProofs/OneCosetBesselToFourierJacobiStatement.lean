import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneCosetBesselToFourierJacobi
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneCoset_besselToFourierJacobi : ∀ D : D7, GlobalTheory.FinPl.OneCosetBF D := by
  first | exact @GlobalTheory.FinPl.oneCosetBF | exact GlobalTheory.FinPl.oneCosetBF | (intros; apply GlobalTheory.FinPl.oneCosetBF <;> assumption)
