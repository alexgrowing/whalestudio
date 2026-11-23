import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PAdicCompletionLaurentEqSumPthPowersModP
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pAdicCompletionLaurent_eq_sum_pthPowers_mod_p : ∀ (p : ℕ) [Fact p.Prime] (x : O0 p), ∃ (g : Fin p → O0 p) (h : O0 p), x = ∑ j : Fin p, qO p ^ (j : ℕ) * g j ^ p + (p : O0 p) * h := by
  first | exact @GlobalTheory.K5.exists_eq_sum_qO_pow_mul_pow_add_mul | exact GlobalTheory.K5.exists_eq_sum_qO_pow_mul_pow_add_mul | (intros; apply GlobalTheory.K5.exists_eq_sum_qO_pow_mul_pow_add_mul <;> assumption)
