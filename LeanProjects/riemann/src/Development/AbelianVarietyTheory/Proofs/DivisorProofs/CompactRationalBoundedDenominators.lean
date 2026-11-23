import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfOrderPullbackAlongHom
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_rational_bounded_denominators : ∀ (p : ℕ) [Fact p.Prime] (Ω : Set (AfP p)), IsCompact Ω → ∃ M : ℕ, 0 < M ∧ ∀ q : ℚ, algebraMap ℚ (AfP p) q ∈ Ω → ∃ (k : ℤ) (e : ℕ), q * ((M : ℚ) * (p : ℚ) ^ e) = k := by
  first | (exact @GlobalTheory.DenAway.den_bounded_of_isCompact) | (exact GlobalTheory.DenAway.den_bounded_of_isCompact) | (intros; apply GlobalTheory.DenAway.den_bounded_of_isCompact <;> assumption)
