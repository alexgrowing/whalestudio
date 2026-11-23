import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_continuousAt_of_continuousAt_apply_of_bounded : ∀ {X : Type} [TopologicalSpace X] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (F : X → SchwartzMap V ℂ) (x0 : X), (∀ v, ContinuousAt (fun x => F x v) x0) →
    (∀ k n : ℕ, ∃ C : ℝ, ∀ᶠ x in nhds x0, ∀ v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x) v‖ ≤ C) → ContinuousAt F x0 := by
  first | exact @GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded | exact GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded | (intros; apply GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded <;> assumption)
