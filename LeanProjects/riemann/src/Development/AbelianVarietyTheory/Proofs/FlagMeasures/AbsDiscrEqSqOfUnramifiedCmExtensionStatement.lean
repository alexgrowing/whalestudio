import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsDiscrEqSqOfUnramifiedCmExtension
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_discr_eq_sq_of_unramified_cmExtension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → |(discr E : ℝ)| = |(discr F : ℝ)| ^ 2 := by
  first | exact @GlobalTheory.SnMass.VolN.abs_discr_eq_abs_discr_sq_of_unramified | exact GlobalTheory.SnMass.VolN.abs_discr_eq_abs_discr_sq_of_unramified | (intros; apply GlobalTheory.SnMass.VolN.abs_discr_eq_abs_discr_sq_of_unramified <;> assumption)
