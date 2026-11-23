import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UniformlyNegDefiniteNearOfContinuousQuadFormFami
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockFormApply
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformly_negDefinite_near_of_continuous_quadForm_family : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ),
    Continuous (fun p : ℝ × V => M p.1 p.2 p.2) → (∀ t v, v ≠ 0 → (M t v v).re < 0) →
    ∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2) := by
  first | exact @GlobalTheory.quadForm_unif_target | exact GlobalTheory.quadForm_unif_target | (intros; apply GlobalTheory.quadForm_unif_target <;> assumption)
