import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedVacuaOfShapeProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawUnfoldedVacuaOfShape_proof : ∀ D : D7, GlobalTheory.SeeSaw.VacOfShape D := by
  first | exact @GlobalTheory.SeeSaw.VacShape.vacOfShape | exact GlobalTheory.SeeSaw.VacShape.vacOfShape | (intros; apply GlobalTheory.SeeSaw.VacShape.vacOfShape <;> assumption)
