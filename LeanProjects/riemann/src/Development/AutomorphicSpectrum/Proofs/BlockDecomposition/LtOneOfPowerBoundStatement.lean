import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LtOneOfPowerBound

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lt_one_of_power_bound : ∀ (δ r : ℝ), 0 < δ → 0 ≤ r → δ⁻¹ * (Real.sqrt δ * r) ^ (2 : ℝ) < 1 → r < 1 := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one | exact GlobalTheory.CompanionTheory.Casselman.lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one | (intros; apply GlobalTheory.CompanionTheory.Casselman.lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one <;> assumption)
