import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePullbackOneVector
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvature_pullback_one_vector : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ} {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {M : Submodule ℤ (Fl g)} {j : Fl g → Pt E g → ℂ} {h : Pt E g → ℝ}, IsDatum B τ M j h → ∀ (β : Fin n → E) (a : Fin n → ℂ) {b : E}, b ∈ B → ∀ (S : Finset (Fin (1 + 1))) (G : (Fin g → ℂ) → Ext (n + n + g)), ContDiff ℝ ∞ G → ∀ (u : ℝ) (z : Fin g → ℂ), curv τ h ![∑ i, a i • β i] b u (fun y => lamL S (pullFullL a (G y))) z = lamL S (pullFullL a (curv τ h β b u G z)) := by
  first | exact @GlobalTheory.TorsionForm.OneVec.CurvPull.curv_pull | exact GlobalTheory.TorsionForm.OneVec.CurvPull.curv_pull | (intros; apply GlobalTheory.TorsionForm.OneVec.CurvPull.curv_pull <;> assumption)
