import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinOpenSubBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_monic_bounded_polynomials : ∀ (K : Type) [Field K] [NumberField K] (d D : ℕ) (B : ℝ), 0 < D → {P : Polynomial K | P.Monic ∧ P.natDegree ≤ d ∧ ∀ k, IsIntegral ℤ ((D : K) * P.coeff k) ∧ ∀ φ : K →+* ℂ, ‖φ (P.coeff k)‖ ≤ B}.Finite := by
  first | (exact @GlobalTheory.finite_monic_coeff_bdd_mul_isIntegral) | (exact GlobalTheory.finite_monic_coeff_bdd_mul_isIntegral) | (intros; apply GlobalTheory.finite_monic_coeff_bdd_mul_isIntegral  <;> assumption)
