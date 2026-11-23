import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NumericalConditionsTheoremTLargePrime
open scoped PowerSeries Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numerical_conditions_theorem_T_large_prime : ∀ (l H N η r : ℕ), 2 ≤ N → 1 ≤ η → η < H → 4 * r ≤ N ^ 2 → 40 * (H * N ^ 2 + N ^ 3) < l → 2 * (H + η + 2 * (N - 1) * r + 1) + 2 < l ∧ 10 * H + 2 ≤ l ∧ 14 * H + (N + 2) * η < l ∧ 8 * H + 1 < l ∧ 4 * η * r + 4 < l ∧ (r + 2) * η < l + 1 := by
  first | exact @GlobalTheory.numerical_bounds_of_forty_mul_lt | exact GlobalTheory.numerical_bounds_of_forty_mul_lt | (intros; apply GlobalTheory.numerical_bounds_of_forty_mul_lt <;> assumption)
