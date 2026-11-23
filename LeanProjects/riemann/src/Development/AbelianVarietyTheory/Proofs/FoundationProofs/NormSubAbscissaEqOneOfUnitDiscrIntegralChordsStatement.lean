import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubAbscissaEqOneOfUnitDiscrIntegralChords
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
theorem _root_.GlobalTheory.T.norm_sub_abscissa_eq_one_of_unitDiscr_integral_chords : ∀ {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (x₁ y₁ x₂ y₂ m m' : ℂ_[p]), ‖W.a₁‖ ≤ 1 → ‖W.a₂‖ ≤ 1 → ‖W.Δ‖ = 1 → W.toAffine.Equation x₁ y₁ → W.toAffine.Equation x₂ y₂ → ‖x₁‖ ≤ 1 → ‖x₂‖ ≤ 1 → x₁ ≠ x₂ → m * (x₁ - x₂) = y₁ - y₂ → m' * (x₁ - x₂) = y₁ - W.toAffine.negY x₂ y₂ → ‖m ^ 2 + W.a₁ * m - W.a₂ - x₁ - x₂‖ ≤ 1 → ‖m' ^ 2 + W.a₁ * m' - W.a₂ - x₁ - x₂‖ ≤ 1 → ‖x₁ - x₂‖ = 1 := by
  first | exact @GlobalTheory.ThetaPar.norm_sub_x_eq_one | exact GlobalTheory.ThetaPar.norm_sub_x_eq_one | (intros; apply GlobalTheory.ThetaPar.norm_sub_x_eq_one <;> assumption)
