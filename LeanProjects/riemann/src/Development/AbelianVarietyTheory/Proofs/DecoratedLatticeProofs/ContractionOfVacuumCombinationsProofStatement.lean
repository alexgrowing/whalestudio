import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContractionOfVacuumCombinationsProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contractionOfVacuumCombinations_proof : ∀ D : D7, GlobalTheory.FinPl.ContrOp D := by
  first | exact @GlobalTheory.FinPl.ContrOpProof.contrOp | exact GlobalTheory.FinPl.ContrOpProof.contrOp | (intros; apply GlobalTheory.FinPl.ContrOpProof.contrOp <;> assumption)
