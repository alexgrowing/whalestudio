import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.HalfVolumeLeviRecursion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.half_volume_levi_recursion : ∀ k r' : ℕ, 1 ≤ k → ∀ x ∈ GV k (1 + r'), ∃ g₁ ∈ GV k r', ∀ y ∈ GV k r', vHalf k (1 + r') (x * ιLev k 1 r' y) = sqLen (x *ᵥ e0 k r') ^ (-(((2 * (1 + r') + k : ℕ) : ℝ) / 2)) * vHalf k r' (g₁ * y) := by
  first | exact @GlobalTheory.HCXi.VLev.vHalf_level | exact GlobalTheory.HCXi.VLev.vHalf_level | (intros; apply GlobalTheory.HCXi.VLev.vHalf_level <;> assumption)
