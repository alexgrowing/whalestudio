import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicNormsAndIntegrality
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_denominator_integral_power : ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (B : ℝ), ∃ m₀ : ℕ, ∀ (c : K) (D : ℕ), (∃ m : ℕ, IsIntegral ℤ ((p : K) ^ m * D * c)) → (∀ φ : K →+* PadicAlgCl p, ‖φ c‖ ≤ B) → IsIntegral ℤ ((p : K) ^ m₀ * D * c) := by
  first | (exact @GlobalTheory.IntAwayP.exists_pow_mul_isIntegral) | (exact GlobalTheory.IntAwayP.exists_pow_mul_isIntegral) | (intros; apply GlobalTheory.IntAwayP.exists_pow_mul_isIntegral <;> assumption)
