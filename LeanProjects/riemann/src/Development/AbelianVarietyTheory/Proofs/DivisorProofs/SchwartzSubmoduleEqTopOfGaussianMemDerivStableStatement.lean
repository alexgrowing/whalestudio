import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSubmoduleEqTopOfGaussianMemDerivStable
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzSubmodule_eq_top_of_gaussian_mem_derivStable : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (N : Submodule ℂ (SchwartzMap V ℂ))
    (g : SchwartzMap V ℂ) (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ), 0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    (∀ x, g x = Complex.exp (-(Q x x))) → g ∈ N →
    (∀ (v : V) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : V →L[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    Dense (N : Set (SchwartzMap V ℂ)) := by
  first | exact @GlobalTheory.SchwartzGaussDense.dense_of_gaussian_mem | exact GlobalTheory.SchwartzGaussDense.dense_of_gaussian_mem | (intros; apply GlobalTheory.SchwartzGaussDense.dense_of_gaussian_mem <;> assumption)
