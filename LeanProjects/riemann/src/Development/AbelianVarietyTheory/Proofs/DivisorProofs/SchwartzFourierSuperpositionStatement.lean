import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFourierSuperposition
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_fourier_superposition : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (ψ : SchwartzMap V ℂ),
    ∃ (m : ℕ) (A : EuclideanSpace ℝ (Fin m) →L[ℝ] (V →L[ℝ] ℝ)) (φ : EuclideanSpace ℝ (Fin m) → ℂ),
      Continuous φ ∧ (∀ n : ℕ, Integrable (fun w => (1 + ‖w‖) ^ n * ‖φ w‖)) ∧
      ∀ x, ψ x = ∫ w, φ w * Complex.exp ((A w x : ℂ) * Complex.I) := by
  first | exact @GlobalTheory.fourier_inversion_real_linear_forms | exact GlobalTheory.fourier_inversion_real_linear_forms | (intros; apply GlobalTheory.fourier_inversion_real_linear_forms <;> assumption)
