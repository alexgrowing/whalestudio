import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.GramPositiveVolumeContinuous
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_positive_volume_continuous : ∀ k r : ℕ, 1 ≤ k → (∀ g ∈ GV k r, ∀ a : Fin (r + 1), 0 < gram k r g a) ∧ (∀ g ∈ GV k r, 0 < vHalf k r g) ∧ (Measurable fun x : Mt k r => vHalf k r (Matrix.of x)) ∧ ContinuousOn (vHalf k r) (GV k r) := by
  first | exact @GlobalTheory.HCXi.GramPos.gram_vHalf_pos_measurable_continuousOn | exact GlobalTheory.HCXi.GramPos.gram_vHalf_pos_measurable_continuousOn | (intros; apply GlobalTheory.HCXi.GramPos.gram_vHalf_pos_measurable_continuousOn <;> assumption)
