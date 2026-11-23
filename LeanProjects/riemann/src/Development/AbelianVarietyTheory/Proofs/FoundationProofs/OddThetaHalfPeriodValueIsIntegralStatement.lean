import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaHalfPeriodValueIsIntegral
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oddTheta_halfPeriod_value_isIntegral : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → TaylorLogMetric.discr Λ = 1 → IsIntegral ℤ (1728 * g2 Λ ^ 3) → ∀ t, 2 * t ∈ Λ → t ∉ Λ → U1 Λ t (sgStar Λ) 0 ≠ 0 ∧ IsIntegral ℤ (U1 Λ t (sgStar Λ) 0) ∧ U1 Λ t (sgStar Λ) 0 ^ 8 = 16 * (g2 Λ - 3 * wpF Λ t ^ 2) ∧ 4 * wpF Λ t ^ 3 - g2 Λ * wpF Λ t - g3 Λ = 0 := by
  first | exact @GlobalTheory.HalfPeriodValue.value_half_period | exact GlobalTheory.HalfPeriodValue.value_half_period | (intros; apply GlobalTheory.HalfPeriodValue.value_half_period <;> assumption)
