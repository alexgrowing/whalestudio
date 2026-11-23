import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormSmulDelSmul
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isForm_smul_del_smul : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (c : ℂ) (α : A.Fld), A.IsForm α → A.IsForm (c • α) ∧ A.del (c • α) = c • A.del α := by
  first | exact @GlobalTheory.CxForm.SmulForm.isForm_smul_and_del_smul | exact GlobalTheory.CxForm.SmulForm.isForm_smul_and_del_smul | (intros; apply GlobalTheory.CxForm.SmulForm.isForm_smul_and_del_smul <;> assumption)
