import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DualInterEqSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_inter_eq_sum' : Dual := by
  first | exact @GlobalTheory.InertZeta.dual_inter_eq_sum | exact GlobalTheory.InertZeta.dual_inter_eq_sum | (intros; apply GlobalTheory.InertZeta.dual_inter_eq_sum <;> assumption)
