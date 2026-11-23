import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtSmallPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_at_small_place : InRange fun _ _ _ _ p j P _ w => SmallAt p j P w → ChiAt p j w := by
  first | exact @GlobalTheory.LevelCharExp.chiAt_inRange | exact GlobalTheory.LevelCharExp.chiAt_inRange | (intros; apply GlobalTheory.LevelCharExp.chiAt_inRange <;> assumption)
