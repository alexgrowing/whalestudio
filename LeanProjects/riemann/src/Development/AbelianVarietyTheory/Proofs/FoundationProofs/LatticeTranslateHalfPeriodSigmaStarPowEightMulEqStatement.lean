import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeTranslateHalfPeriodSigmaStarPowEightMulEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTranslate_halfPeriod_sigmaStar_pow_eight_mul_eq_one : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t : ℂ, t ∉ Λ → 2 * t ∈ Λ → U1 Λ t (sgStar Λ) 0 ^ 8 * ((wpF Λ t ^ 2 + g2 Λ / 4) ^ 2 + 2 * g3 Λ * wpF Λ t) = 1 := by
  first | exact @GlobalTheory.HalfPeriodValue.U1_sgStar_pow_eight | exact GlobalTheory.HalfPeriodValue.U1_sgStar_pow_eight | (intros; apply GlobalTheory.HalfPeriodValue.U1_sgStar_pow_eight <;> assumption)
