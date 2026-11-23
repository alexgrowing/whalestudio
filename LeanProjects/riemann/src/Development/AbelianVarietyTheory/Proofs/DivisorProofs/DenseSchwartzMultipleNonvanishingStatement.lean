import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseSchwartzMultipleNonvanishing
import Mathlib
open SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_schwartz_multiple_nonvanishing : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (g : SchwartzMap V ℂ), (∀ x, g x ≠ 0) → Dense {φ : SchwartzMap V ℂ | HasCompactSupport (⇑φ)} →
    Dense {F : SchwartzMap V ℂ | ∃ ψ : SchwartzMap V ℂ, ∀ x, F x = ψ x * g x} := by
  first | exact @GlobalTheory.dense_schwartz_mul_of_ne_zero | exact GlobalTheory.dense_schwartz_mul_of_ne_zero | (intros; apply GlobalTheory.dense_schwartz_mul_of_ne_zero <;> assumption)
