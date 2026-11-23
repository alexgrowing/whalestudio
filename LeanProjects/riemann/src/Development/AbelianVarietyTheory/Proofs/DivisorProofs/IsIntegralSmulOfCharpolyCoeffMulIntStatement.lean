import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSmulOfCharpolyCoeffMulInt
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_natCast_smul_of_mul_charpoly_coeff_int : ∀ (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (x : A) (M : ℕ), (∀ i, ∃ a : ℤ, (M : ℚ) * (LinearMap.mulLeft ℚ x).charpoly.coeff i = a) → IsIntegral ℤ ((M : ℤ) • x) := by
  first | (exact @GlobalTheory.isIntegral_smul_of_charpoly_coeff_mul_int) | (exact GlobalTheory.isIntegral_smul_of_charpoly_coeff_mul_int) | (intros; apply GlobalTheory.isIntegral_smul_of_charpoly_coeff_mul_int  <;> assumption)
