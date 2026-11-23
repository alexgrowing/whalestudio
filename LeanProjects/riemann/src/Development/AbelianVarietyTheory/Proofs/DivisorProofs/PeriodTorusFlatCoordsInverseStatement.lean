import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodTorusFlatCoordsInverse
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_torus_flat_coords_inverse : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ b ∈ B, (∀ x, flatOf (τ b) (per (τ b) x) = x) ∧ ∀ z, per (τ b) (flatOf (τ b) z) = z := by
  first | exact @GlobalTheory.flatcoord_inverse | exact GlobalTheory.flatcoord_inverse | (intros; apply GlobalTheory.flatcoord_inverse <;> assumption)
