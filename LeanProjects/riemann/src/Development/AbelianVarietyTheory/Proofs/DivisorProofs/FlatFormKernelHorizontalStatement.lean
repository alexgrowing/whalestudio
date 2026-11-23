import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormKernelHorizontal
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_form_kernel_horizontal : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → (∀ P ∈ cov B g, ∀ v : Pt E g, (∀ w : Fin g → ℂ, om0 τ P ![v, (0, w)] = 0) ↔ dflat τ P v = 0) ∧ (∀ P ∈ cov B g, (∀ v : Pt E g, dflat τ P v = 0 → dflat τ P (Complex.I • v) = 0) ∧ ∀ u : E, ∃! w : Fin g → ℂ, dflat τ P (u, w) = 0) := by
  first | exact @GlobalTheory.FlatKernel.orth | exact GlobalTheory.FlatKernel.orth | (intros; apply GlobalTheory.FlatKernel.orth <;> assumption)
