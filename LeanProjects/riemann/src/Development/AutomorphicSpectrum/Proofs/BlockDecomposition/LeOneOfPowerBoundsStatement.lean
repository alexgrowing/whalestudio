import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeOneOfPowerBounds

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_one_of_power_bounds : ∀ (δ r : ℝ), 0 < δ → δ < 1 → 0 ≤ r → (∀ ε : ℝ, 0 < ε → δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε) < 1) → r ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.le_one_of_forall_sqrt_mul_rpow_lt | exact GlobalTheory.CompanionTheory.Casselman.le_one_of_forall_sqrt_mul_rpow_lt | (intros; apply GlobalTheory.CompanionTheory.Casselman.le_one_of_forall_sqrt_mul_rpow_lt <;> assumption)
