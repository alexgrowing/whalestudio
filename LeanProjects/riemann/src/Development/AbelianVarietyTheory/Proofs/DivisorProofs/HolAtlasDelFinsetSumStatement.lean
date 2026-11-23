import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasDelFinsetSum
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holAtlas_del_finset_sum : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {N : ℕ} (α : Fin N → A.Fld), (∀ j, A.IsForm (α j)) → A.del (∑ j, α j) = ∑ j, A.del (α j) := by
  first | exact @GlobalTheory.CxForm.HolAtlas.del_finset_sum | exact GlobalTheory.CxForm.HolAtlas.del_finset_sum | (intros; apply GlobalTheory.CxForm.HolAtlas.del_finset_sum <;> assumption)
