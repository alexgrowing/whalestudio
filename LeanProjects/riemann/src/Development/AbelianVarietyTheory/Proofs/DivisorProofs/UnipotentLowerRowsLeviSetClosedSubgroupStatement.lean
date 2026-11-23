import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentLowerRowsLeviSetClosedSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableToGLEntry
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentLowerRowsLeviSet_closed_subgroup : ∀ (n r : ℕ), (∀ g ∈ levSet n r, ∀ h ∈ levSet n r, g * h ∈ levSet n r) ∧ (∀ g ∈ levSet n r, g⁻¹ ∈ levSet n r) ∧ (∀ u ∈ GlobalTheory.SmGL.unipB ℂ (Fin n), u ∈ levSet n r) ∧ IsClosed (levSet n r) := by
  first | exact @GlobalTheory.JSW.levSet_closed_subgroup | exact GlobalTheory.JSW.levSet_closed_subgroup | (intros; apply GlobalTheory.JSW.levSet_closed_subgroup <;> assumption)
