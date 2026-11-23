import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallPairPairingAtOneGluedPlace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallPair_pairing_at_one_gluedPlace : ∀ D : D7, GlobalTheory.FinPl.SmallOne D := by
  first | exact @GlobalTheory.FinPl.smallOne | exact GlobalTheory.FinPl.smallOne | (intros; apply GlobalTheory.FinPl.smallOne <;> assumption)
