import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique : ∀ D : D7, GlobalTheory.FinPl.OverBasic D := by
  first | exact @GlobalTheory.FinPl.overBasic | exact GlobalTheory.FinPl.overBasic | (intros; apply GlobalTheory.FinPl.overBasic <;> assumption)
