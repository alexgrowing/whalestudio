import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddMulLeOfPowLeOfLarge
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.add_mul_le_of_pow_le_of_large : ∀ (p L m : ℕ), 2 ≤ p → ∃ M0 : ℕ, ∀ n v : ℕ, M0 ≤ n → p ^ v ≤ n → (v + m) * L ≤ n := by
  first | exact @GlobalTheory.VSubArith.add_mul_le_of_pow_le | exact GlobalTheory.VSubArith.add_mul_le_of_pow_le | (intros; apply GlobalTheory.VSubArith.add_mul_le_of_pow_le <;> assumption)
