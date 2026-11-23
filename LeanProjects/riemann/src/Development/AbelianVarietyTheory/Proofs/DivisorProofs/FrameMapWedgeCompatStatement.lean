import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMapWedgeCompat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMap_wedge_compat : ∀ {g : ℕ} (n : ℕ) (D : Matrix (Fin g) (Fin g) ℂ) (w : Ext (n + n + g)), (∀ c : Fin g, frameMap n D (wedge (dzb n c) w) = ∑ a, star (D⁻¹ a c) • wedge (dzb n a) (frameMap n D w)) ∧ ∀ i : Fin n, frameMap n D (wedge (dt g i) w) = wedge (dt g i) (frameMap n D w) ∧ frameMap n D (wedge (dtb g i) w) = wedge (dtb g i) (frameMap n D w) := by
  first | exact @GlobalTheory.TorsionForm.FrameWedge.frameMap_wedge | exact GlobalTheory.TorsionForm.FrameWedge.frameMap_wedge | (intros; apply GlobalTheory.TorsionForm.FrameWedge.frameMap_wedge <;> assumption)
