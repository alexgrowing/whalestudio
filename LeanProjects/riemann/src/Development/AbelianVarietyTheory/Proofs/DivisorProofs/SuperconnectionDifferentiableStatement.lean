import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnectionDifferentiable
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.superconnection_differentiable : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g m : ℕ} {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {M : Submodule ℤ (Fl g)} {j : Fl g → Pt E g → ℂ} {h : Pt E g → ℝ}, IsDatum B τ M j h → ∀ (β : Fin m → E) {b : E}, b ∈ B → ∀ (G : (Fin g → ℂ) → Ext (m + m + g)), ContDiff ℝ ∞ G → ∀ (u : ℝ) (z : Fin g → ℂ), DifferentiableAt ℝ (superconn τ h β u fun P => G P.2) (b, z) := by
  first | exact @GlobalTheory.SuperconnDiff.superconn_differentiableAt | exact GlobalTheory.SuperconnDiff.superconn_differentiableAt | (intros; apply GlobalTheory.SuperconnDiff.superconn_differentiableAt <;> assumption)
