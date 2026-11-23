import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierModulatedSchwartzBounds
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_modulated_schwartz_bounds : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (g : SchwartzMap V ℂ),
    ∃ H : (V →L[ℝ] ℝ) → SchwartzMap V ℂ, (∀ ξ x, H ξ x = Complex.exp ((ξ x : ℂ) * Complex.I) * g x) ∧
      ∀ k n : ℕ, ∃ C : ℝ, ∀ ξ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (H ξ) x‖ ≤ C * (1 + ‖ξ‖) ^ n := by
  first | exact @GlobalTheory.SchwartzCharMul.exists_charMul_schwartz_bound | exact GlobalTheory.SchwartzCharMul.exists_charMul_schwartz_bound | (intros; apply GlobalTheory.SchwartzCharMul.exists_charMul_schwartz_bound <;> assumption)
