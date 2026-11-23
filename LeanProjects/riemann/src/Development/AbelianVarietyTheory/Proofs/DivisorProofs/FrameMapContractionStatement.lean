import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMapContraction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMap_contraction : ∀ {g : ℕ} (n : ℕ) (D : Matrix (Fin g) (Fin g) ℂ), IsUnit D → ∀ (d : Fin g) (w : Ext (n + n + g)), frameMap n D (contr (dzb n d) w) = ∑ a, star (D d a) • contr (dzb n a) (frameMap n D w) := by
  first | exact @GlobalTheory.TorsionForm.FrameContr.frameMap_contr_dzb | exact GlobalTheory.TorsionForm.FrameContr.frameMap_contr_dzb | (intros; apply GlobalTheory.TorsionForm.FrameContr.frameMap_contr_dzb <;> assumption)
