import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesFormType
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_preserves_form_type : ∀ (n m : ℕ) (L : V n →L[ℂ] V m) (p q : ℕ) (α : Alt m), IsType p q α → IsType p q (pull L α) := by
  first | exact @GlobalTheory.CxForm.isType_pull_linear | exact GlobalTheory.CxForm.isType_pull_linear | (intros; apply GlobalTheory.CxForm.isType_pull_linear <;> assumption)
