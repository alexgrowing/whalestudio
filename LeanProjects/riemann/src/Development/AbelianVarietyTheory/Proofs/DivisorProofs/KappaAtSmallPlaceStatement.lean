import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaAtSmallPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappa_at_small_place : InRange fun _ _ _ _ p j P _ w => SmallAt p j P w → KapAt p j P w := by
  first | exact @GlobalTheory.FrameOf.kapSt | exact GlobalTheory.FrameOf.kapSt | (intros; apply GlobalTheory.FrameOf.kapSt <;> assumption)
