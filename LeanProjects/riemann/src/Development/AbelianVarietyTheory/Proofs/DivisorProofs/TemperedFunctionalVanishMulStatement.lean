import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TemperedFunctionalVanishMul
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tempered_functional_vanish_mul : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (T : SchwartzMap V ℂ →L[ℂ] ℂ)
    (g : SchwartzMap V ℂ), (∀ (ξ : V →L[ℝ] ℝ) (h : SchwartzMap V ℂ), (∀ x, h x = Complex.exp ((ξ x : ℂ) * Complex.I) * g x) → T h = 0) →
    ∀ (ψ h : SchwartzMap V ℂ), (∀ x, h x = g x * ψ x) → T h = 0 := by
  first | exact @GlobalTheory.kill_schwartz_multiple_of_kill_characters | exact GlobalTheory.kill_schwartz_multiple_of_kill_characters | (intros; apply GlobalTheory.kill_schwartz_multiple_of_kill_characters <;> assumption)
