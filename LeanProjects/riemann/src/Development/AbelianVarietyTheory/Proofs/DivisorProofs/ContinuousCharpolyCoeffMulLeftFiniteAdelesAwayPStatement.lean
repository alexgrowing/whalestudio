import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharpolyCoeffMulLeftFiniteAdelesAwayP
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_charpoly_coeff_mulLeft_finiteAdeles_awayP : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (k : ℕ), Continuous fun g : G.GAf => (LinearMap.charpoly (LinearMap.mulLeft (AfP p) (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C))).coeff k := by
  first | (exact @GlobalTheory.charpoly_coeff_continuous_GAf) | (exact GlobalTheory.charpoly_coeff_continuous_GAf) | (intros; apply GlobalTheory.charpoly_coeff_continuous_GAf  <;> assumption)
