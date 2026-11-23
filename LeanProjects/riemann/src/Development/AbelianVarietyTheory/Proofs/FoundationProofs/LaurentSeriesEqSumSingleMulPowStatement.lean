import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesEqSumSingleMulPow
import Mathlib
open scoped NNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentSeries_eq_sum_single_mul_pow_prime : ∀ (p : ℕ) [Fact p.Prime] (f : LaurentSeries (ZMod p)), ∃ g : Fin p → LaurentSeries (ZMod p), f = ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ZMod p) * g j ^ p := by
  first | exact @GlobalTheory.laurentSeries_eq_sum_single_mul_pow | exact GlobalTheory.laurentSeries_eq_sum_single_mul_pow | (intros; apply GlobalTheory.laurentSeries_eq_sum_single_mul_pow <;> assumption)
