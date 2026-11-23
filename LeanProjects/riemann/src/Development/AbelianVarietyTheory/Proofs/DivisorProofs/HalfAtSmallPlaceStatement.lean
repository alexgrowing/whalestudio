import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfAtSmallPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.half_at_small_place : InRange fun Fm x _ i p j P _ w => SmallAt p j P w → HalfAt (Fm.D x i) (Formalism.EigenvalueLevelCeiling.plc w) := by
  first | exact @GlobalTheory.HalfLabels.halfAt_inRange | exact GlobalTheory.HalfLabels.halfAt_inRange | (intros; apply GlobalTheory.HalfLabels.halfAt_inRange <;> assumption)
