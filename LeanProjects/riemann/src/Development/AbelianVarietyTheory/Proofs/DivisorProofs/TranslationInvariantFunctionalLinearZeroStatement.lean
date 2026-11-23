import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalLinearZero
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulation_invariant_functional_kills_linear_multiple : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →ₗ[ℂ] ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ), (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) →
    ∀ (L : V →L[ℝ] ℝ) (h g : SchwartzMap V ℂ), (∀ x, g x = (L x : ℂ) * h x) → T g = 0 := by
  first | exact @GlobalTheory.CharInvForm.kills_linear_mul | exact GlobalTheory.CharInvForm.kills_linear_mul | (intros; apply GlobalTheory.CharInvForm.kills_linear_mul <;> assumption)
