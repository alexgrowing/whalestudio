import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMatrixOneParameterGroupEqExp
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_matrix_oneParameterGroup_eq_exp : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℝ → Matrix ι ι ℝ), Continuous M → M 0 = 1 → (∀ s t, M (s + t) = M s * M t) → ∃ X : Matrix ι ι ℝ, ∀ t, M t = NormedSpace.exp (t • X) := by
  first | exact @GlobalTheory.matrix_oneParamGroup_eq_exp | exact GlobalTheory.matrix_oneParamGroup_eq_exp | (intros; apply GlobalTheory.matrix_oneParamGroup_eq_exp <;> assumption)
