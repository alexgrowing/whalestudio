import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epsilonFourierProduct_bijective_gluedPlaces : ∀ D : D7, GlobalTheory.FinPl.AllBijective D := by
  first | exact @GlobalTheory.FinPl.allBijective_all | exact GlobalTheory.FinPl.allBijective_all | (intros; apply GlobalTheory.FinPl.allBijective_all <;> assumption)
