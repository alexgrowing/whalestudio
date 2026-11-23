import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzDoubleIntegralExists
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_double_integral_exists : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (μα : Measure α) (μβ : Measure β) (Fm : α → β → SchwartzMap V ℂ),
    (∀ (m : ℕ) (t : V) (k : α), AEStronglyMeasurable (fun l => iteratedFDeriv ℝ m (Fm k l) t) μβ) →
    (∀ (m : ℕ) (t : V), AEStronglyMeasurable (fun k => ∫ l, iteratedFDeriv ℝ m (Fm k l) t ∂μβ) μα) →
    (∀ n m : ℕ, ∃ Bd : α → β → ℝ, (∀ k, Integrable (Bd k) μβ) ∧ Integrable (fun k => ∫ l, Bd k l ∂μβ) μα ∧
      ∀ k l t, ‖t‖ ^ n * ‖iteratedFDeriv ℝ m (Fm k l) t‖ ≤ Bd k l) →
    ∃ g : SchwartzMap V ℂ, ∀ t, g t = ∫ k, ∫ l, Fm k l t ∂μβ ∂μα := by
  first | exact @GlobalTheory.schwartz_iterated_integral_of_dominated | exact GlobalTheory.schwartz_iterated_integral_of_dominated | (intros; apply GlobalTheory.schwartz_iterated_integral_of_dominated <;> assumption)
