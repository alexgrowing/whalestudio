import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFourierRepresentation
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_fourier_representation : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (m : SchwartzMap V ℂ),
    ∃ (d : ℕ) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] V →L[ℝ] ℝ) (h : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ),
    ∀ x, m x = ∫ ξ, h ξ * Complex.exp (Complex.I * (A ξ x : ℂ)) := by
  first | exact @GlobalTheory.schwartz_eq_fourier_synthesis | exact GlobalTheory.schwartz_eq_fourier_synthesis | (intros; apply GlobalTheory.schwartz_eq_fourier_synthesis <;> assumption)
