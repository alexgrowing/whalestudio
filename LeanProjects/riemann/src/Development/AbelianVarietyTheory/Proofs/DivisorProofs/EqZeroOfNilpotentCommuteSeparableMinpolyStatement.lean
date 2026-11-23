import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfNilpotentCommuteSeparableMinpoly
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsConjOfMinpolyEqOfSeparable
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_nilpotent_commute_separable_minpoly : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (y₀ : G.C), (minpoly G.F y₀).Separable →
    (minpoly G.F y₀).natDegree = G.n → ∀ x : G.C, Commute x y₀ → ∀ k : ℕ, x ^ k = 0 → x = 0 := by
  first | (exact @GlobalTheory.LKCx.ClsReg.eq_zero_of_commute_of_pow_eq_zero) | (exact GlobalTheory.LKCx.ClsReg.eq_zero_of_commute_of_pow_eq_zero) | (intros; apply GlobalTheory.LKCx.ClsReg.eq_zero_of_commute_of_pow_eq_zero <;> assumption)
