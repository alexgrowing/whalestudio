import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapPreservesVacuumProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMapPreservesVacuum_proof : ∀ D : D7, GlobalTheory.FinPl.FlatVac D := by
  first | exact @GlobalTheory.FinPl.FlatVacuum.flatVac | exact GlobalTheory.FinPl.FlatVacuum.flatVac | (intros; apply GlobalTheory.FinPl.FlatVacuum.flatVac <;> assumption)
