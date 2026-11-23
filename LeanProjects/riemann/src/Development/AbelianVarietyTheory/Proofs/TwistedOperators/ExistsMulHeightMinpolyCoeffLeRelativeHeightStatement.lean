import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMulHeightMinpolyCoeffLeRelativeHeight
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneLeHtE

open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mulHeight_minpoly_coeff_le_relativeHeight : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (c : ℝ) (a : ℕ), ∀ (x : E) (j : ℕ), Height.mulHeight₁ ((minpoly F x).coeff j) ≤ c * (GlobalTheory.RatCount.htE F x : ℝ) ^ a := by
  first | exact @GlobalTheory.RatCount.CoefHt.exists_mulHeight_coeff_minpoly_le | exact GlobalTheory.RatCount.CoefHt.exists_mulHeight_coeff_minpoly_le | (intros; apply GlobalTheory.RatCount.CoefHt.exists_mulHeight_coeff_minpoly_le <;> assumption)
