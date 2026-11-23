import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormDbar
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isForm_dbar' : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld), A.IsForm α → A.IsForm (A.dbar α) := by
  first | exact @GlobalTheory.CxForm.isForm_dbar | exact GlobalTheory.CxForm.isForm_dbar | (intros; apply GlobalTheory.CxForm.isForm_dbar <;> assumption)
