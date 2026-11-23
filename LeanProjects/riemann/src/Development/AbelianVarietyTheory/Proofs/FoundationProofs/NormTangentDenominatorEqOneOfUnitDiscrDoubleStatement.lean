import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormTangentDenominatorEqOneOfUnitDiscrDouble
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLe
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_tangentDenominator_eq_one_of_unitDiscr_double : ∀ {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (x y m : ℂ_[p]), ‖W.a₁‖ ≤ 1 → ‖W.a₂‖ ≤ 1 → ‖W.a₃‖ ≤ 1 → ‖W.a₄‖ ≤ 1 → ‖W.a₆‖ ≤ 1 → ‖W.Δ‖ = 1 → W.toAffine.Equation x y → ‖x‖ ≤ 1 → 2 * y + W.a₁ * x + W.a₃ ≠ 0 → m * (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y → ‖m ^ 2 + W.a₁ * m - W.a₂ - 2 * x‖ ≤ 1 → ‖2 * y + W.a₁ * x + W.a₃‖ = 1 := by
  first | exact @GlobalTheory.ThetaPar.unit_of_double_integral | exact GlobalTheory.ThetaPar.unit_of_double_integral | (intros; apply GlobalTheory.ThetaPar.unit_of_double_integral <;> assumption)
