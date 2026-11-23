import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightInvariantEqSumOpenSubgroupCosets
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets : CosetIntegral := by
  first | exact @GlobalTheory.InertZeta.cosetIntegral_holds | exact GlobalTheory.InertZeta.cosetIntegral_holds | (intros; apply GlobalTheory.InertZeta.cosetIntegral_holds <;> assumption)
