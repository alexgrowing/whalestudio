import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureFormVerticalRiemann
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvature_form_vertical_riemann : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ} {B : Set E}
    {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ) {b : E} (hb : b ∈ B)
    (z v w : Fin g → ℂ),
    om0 τ (b, z) ![(0, v), (0, w)] = riem (flatOf (τ b) v) (flatOf (τ b) w) := by
  first | exact @GlobalTheory.TorsionForm.FlatAcyc.curvature_vertical | exact GlobalTheory.TorsionForm.FlatAcyc.curvature_vertical | (intros; apply GlobalTheory.TorsionForm.FlatAcyc.curvature_vertical <;> assumption)
