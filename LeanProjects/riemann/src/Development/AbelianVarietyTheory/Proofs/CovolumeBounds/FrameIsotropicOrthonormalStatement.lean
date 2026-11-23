import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FrameIsotropicOrthonormal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_isotropic_orthonormal : ∀ k r : ℕ, 1 ≤ k → (frame k r)ᴴ * frame k r = 1 ∧ (frame k r)ᴴ * Hpk k r * frame k r = 0 := by
  first | exact @GlobalTheory.HCXi.FrameOrth.frame_orthonormal_isotropic | exact GlobalTheory.HCXi.FrameOrth.frame_orthonormal_isotropic | (intros; apply GlobalTheory.HCXi.FrameOrth.frame_orthonormal_isotropic <;> assumption)
