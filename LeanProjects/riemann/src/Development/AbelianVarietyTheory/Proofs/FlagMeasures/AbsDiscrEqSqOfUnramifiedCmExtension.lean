import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory.SnMass.VolN

theorem abs_discr_eq_abs_discr_sq_of_unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → |(discr E : ℝ)| = |(discr F : ℝ)| ^ 2 := by
  intro F E _ _ _ _ _ σ hcm hu
  have hd := (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hu
  have h1 := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)
  rw [hd, Ideal.absNorm_top, one_mul, hcm.2.2.1] at h1
  have h2 : (((discr E).natAbs : ℕ) : ℝ) = (((discr F).natAbs ^ 2 : ℕ) : ℝ) := by exact_mod_cast h1
  simpa [Nat.cast_natAbs] using h2

end GlobalTheory.SnMass.VolN
