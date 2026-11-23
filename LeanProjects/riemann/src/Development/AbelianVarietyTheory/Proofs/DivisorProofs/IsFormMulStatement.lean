import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormMul
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isForm_mul_of_isForm_of_isForm : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α β : A.Fld), A.IsForm α → A.IsForm β → A.IsForm (α * β) := by
  first | exact @GlobalTheory.CxForm.FormMul.isForm_mul | exact GlobalTheory.CxForm.FormMul.isForm_mul | (intros; apply GlobalTheory.CxForm.FormMul.isForm_mul <;> assumption)
