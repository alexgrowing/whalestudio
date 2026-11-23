import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffFormalGroupLawEvalPointsOfDegreeLeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_formalGroupLawEvalPoints_of_degree_le_one : ∀ {B O : Type} [CommRing B] [CommRing O] (θ : B →+* O) {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}, IsLift θ μ → ∀ {τ : Type} (u v : Fin d → MvPowerSeries τ B), (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) → ∀ (i : Fin d) (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (op μ u v i) = coeff β (u i + v i) := by
  first | exact @GlobalTheory.QLog.OpLin.coeff_op_of_degree_le_one | exact GlobalTheory.QLog.OpLin.coeff_op_of_degree_le_one | (intros; apply GlobalTheory.QLog.OpLin.coeff_op_of_degree_le_one <;> assumption)
