import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ParabolicLineStabilizerLevi
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_line_stabilizer_levi : ∀ (k r' : ℕ) (a : ℂ), ∀ p ∈ GV k (1 + r'), p *ᵥ e0 k r' = a • e0 k r' → a ≠ 0 ∧ ∃ g₁ ∈ GV k r', ∀ w : Fin (2 * r' + k + 1) → ℂ, ∃ c : ℂ, p *ᵥ liftVec k 1 r' w = liftVec k 1 r' (g₁ *ᵥ w) + c • e0 k r' := by
  first | exact @GlobalTheory.HCXi.LineStabiliser.acts_through_level_one | exact GlobalTheory.HCXi.LineStabiliser.acts_through_level_one | (intros; apply GlobalTheory.HCXi.LineStabiliser.acts_through_level_one <;> assumption)
