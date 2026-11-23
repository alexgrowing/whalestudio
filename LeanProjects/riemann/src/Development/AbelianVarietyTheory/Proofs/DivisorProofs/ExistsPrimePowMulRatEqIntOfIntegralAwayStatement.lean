import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulRatEqIntOfIntegralAway
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_pow_mul_rat_eq_int_of_integral_away : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), (∀ v : AwayP p, algebraMap ℚ (v.1.adicCompletion ℚ) q ∈ v.1.adicCompletionIntegers ℚ) → ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * q = z := by
  first | (exact @GlobalTheory.ratint_away) | (exact GlobalTheory.ratint_away) | (intros; apply GlobalTheory.ratint_away  <;> assumption)
