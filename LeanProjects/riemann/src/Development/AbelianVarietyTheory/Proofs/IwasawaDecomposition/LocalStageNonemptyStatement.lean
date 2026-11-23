import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalStageNonempty
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_stage_nonempty : Nonempty GlobalTheory.Mem.LocStage := by
  first | exact @GlobalTheory.Mem.nonempty_locStage | exact GlobalTheory.Mem.nonempty_locStage | (intros; apply GlobalTheory.Mem.nonempty_locStage <;> assumption)
