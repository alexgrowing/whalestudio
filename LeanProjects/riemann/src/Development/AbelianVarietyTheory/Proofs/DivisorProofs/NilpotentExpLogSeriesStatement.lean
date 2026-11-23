import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentExpLogSeries
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilpotent_exp_log_series : ∀ (A : Type) [Ring A] [Algebra ℚ A] (D : ℕ) (n : A), n ^ D = 0 → IsNilpotent.exp (∑ j ∈ Finset.range D, ((-1 : ℚ) ^ j / ((j : ℚ) + 1)) • n ^ (j + 1)) = 1 + n := by
  first | exact @GlobalTheory.NilpExpLog.exp_truncLog_one_add | exact GlobalTheory.NilpExpLog.exp_truncLog_one_add | (intros; apply GlobalTheory.NilpExpLog.exp_truncLog_one_add <;> assumption)
