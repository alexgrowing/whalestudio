import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapFlatDerivative
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_map_flat_derivative : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ b ∈ B, ∀ z v : Fin g → ℂ, dflat τ (b, z) ((0 : E), v) = flatOf (τ b) v := by
  first | exact @GlobalTheory.FlatVert.dflat_vert | exact GlobalTheory.FlatVert.dflat_vert | (intros; apply GlobalTheory.FlatVert.dflat_vert <;> assumption)
