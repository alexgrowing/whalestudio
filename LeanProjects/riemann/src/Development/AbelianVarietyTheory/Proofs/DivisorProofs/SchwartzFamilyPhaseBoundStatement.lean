import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFamilyPhaseBound
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_family_phase_bound : ∀ (E P : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P →L[ℝ] E →L[ℝ] ℝ) (f : SchwartzMap E ℂ), ∃ Φ : P → SchwartzMap E ℂ,
    (∀ ξ x, Φ ξ x = Complex.exp (Complex.I * (A ξ x : ℂ)) * f x) ∧ Continuous Φ ∧
    ∀ k n : ℕ, ∃ C : ℝ, ∀ ξ, SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ C * (1 + ‖ξ‖ ^ n) := by
  first | exact @GlobalTheory.CharFamily.charMul_family | exact GlobalTheory.CharFamily.charMul_family | (intros; apply GlobalTheory.CharFamily.charMul_family <;> assumption)
