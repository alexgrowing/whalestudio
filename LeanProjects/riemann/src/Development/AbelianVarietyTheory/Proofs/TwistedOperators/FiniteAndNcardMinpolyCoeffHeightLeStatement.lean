import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndNcardMinpolyCoeffHeightLe
import Mathlib

open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_and_ncard_minpoly_coeff_height_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B → {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.Finite ∧ (({x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.ncard : ℕ) : ℝ) ≤ C * B ^ k := by
  first | exact @GlobalTheory.MinpolyHeightCount.finite_and_ncard_minpoly_height_le | exact GlobalTheory.MinpolyHeightCount.finite_and_ncard_minpoly_height_le | (intros; apply GlobalTheory.MinpolyHeightCount.finite_and_ncard_minpoly_height_le <;> assumption)
