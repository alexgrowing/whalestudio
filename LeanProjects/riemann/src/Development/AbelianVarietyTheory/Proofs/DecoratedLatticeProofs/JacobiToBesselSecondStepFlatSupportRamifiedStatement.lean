import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselSecondStepFlatSupportRamified
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobiToBessel_second_step_flat_support_ramified : ∀ D : D7, GlobalTheory.FinPl.SuppSecond D := by
  first | exact @GlobalTheory.FinPl.suppSecond_holds | exact GlobalTheory.FinPl.suppSecond_holds | (intros; apply GlobalTheory.FinPl.suppSecond_holds <;> assumption)
