import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormVerticalNegativeImagPositive
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_form_vertical_negative_imag_positive : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → (∀ P ∈ cov B g, ∀ v w : Fin g → ℂ, om0 τ P ![(0, v), (0, w)] = -(herm (τ P.1) v w).im) ∧ (∀ P ∈ cov B g, ∀ v : Fin g → ℂ, v ≠ 0 → 0 < om0 τ P ![(0, v), (0, Complex.I • v)]) := by
  first | exact @GlobalTheory.FlatFibre.flat_fibre | exact GlobalTheory.FlatFibre.flat_fibre | (intros; apply GlobalTheory.FlatFibre.flat_fibre <;> assumption)
