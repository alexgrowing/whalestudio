import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureSumOfSections
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvature_sum_of_sections : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g m : ℕ} {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {M : Submodule ℤ (Fl g)} {j : Fl g → Pt E g → ℂ} {h : Pt E g → ℝ}, IsDatum B τ M j h → ∀ (β : Fin m → E) {b : E}, b ∈ B → ∀ {ι : Type} (s : Finset ι) (G : ι → (Fin g → ℂ) → Ext (m + m + g)), (∀ i, ContDiff ℝ ∞ (G i)) → ∀ (u : ℝ) (z : Fin g → ℂ), curv τ h β b u (fun y => ∑ i ∈ s, G i y) z = ∑ i ∈ s, curv τ h β b u (G i) z := by
  first | exact @GlobalTheory.TorsionForm.OneVec.curv_sum | exact GlobalTheory.TorsionForm.OneVec.curv_sum | (intros; apply GlobalTheory.TorsionForm.OneVec.curv_sum <;> assumption)
