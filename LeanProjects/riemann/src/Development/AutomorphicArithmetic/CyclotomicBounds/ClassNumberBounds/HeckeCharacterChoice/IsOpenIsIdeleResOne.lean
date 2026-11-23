import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.PrincipalIdele

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.Choice

open KStar.IdealValuations

variable {E : Type*} [Field E] [NumberField E] {𝔪 : Ideal (𝓞 E)}

private noncomputable def resExp (𝔪 : Ideal (𝓞 E)) (v : HeightOneSpectrum (𝓞 E)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors

private theorem finite_above (h𝔪 : 𝔪 ≠ ⊥) :
    {v : HeightOneSpectrum (𝓞 E) | 𝔪 ≤ v.asIdeal}.Finite := by
  simpa only [Ideal.dvd_iff_le] using Ideal.finite_factors h𝔪

end KStar.Choice
