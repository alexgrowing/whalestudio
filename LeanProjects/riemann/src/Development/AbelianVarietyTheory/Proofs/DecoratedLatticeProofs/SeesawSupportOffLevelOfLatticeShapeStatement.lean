import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawSupportOffLevelOfLatticeShape
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_support_off_level_of_lattice_shape : ∀ D : D7, GlobalTheory.SeeSaw.OffOfShape D := by
  first | exact @GlobalTheory.SeeSaw.offOfShape_all | exact GlobalTheory.SeeSaw.offOfShape_all | (intros; apply GlobalTheory.SeeSaw.offOfShape_all <;> assumption)
