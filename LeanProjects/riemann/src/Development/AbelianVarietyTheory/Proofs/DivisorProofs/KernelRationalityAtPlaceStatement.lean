import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelRationalityAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_rationality_at_place : KerOfAt := by
  first | exact @GlobalTheory.BigOn.Exp.SerBase.kerOfAt | exact GlobalTheory.BigOn.Exp.SerBase.kerOfAt | (intros; apply GlobalTheory.BigOn.Exp.SerBase.kerOfAt <;> assumption)
