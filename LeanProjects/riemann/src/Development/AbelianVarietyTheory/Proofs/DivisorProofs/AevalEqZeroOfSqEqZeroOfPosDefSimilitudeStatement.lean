import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalEqZeroOfSqEqZeroOfPosDefSimilitude
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_eq_zero_of_sq_eq_zero_of_posDef_similitude : ∀ (n : ℕ) (H M : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), H.PosDef → 0 < s → Mᴴ * H * M = (s : ℂ) • H → ∀ P : Polynomial ℂ, Polynomial.aeval M P * Polynomial.aeval M P = 0 → Polynomial.aeval M P = 0 := by
  first | (exact @GlobalTheory.aeval_eq_zero_of_mul_self_eq_zero_of_similitude) | (exact GlobalTheory.aeval_eq_zero_of_mul_self_eq_zero_of_similitude) | (intros; apply GlobalTheory.aeval_eq_zero_of_mul_self_eq_zero_of_similitude  <;> assumption)
