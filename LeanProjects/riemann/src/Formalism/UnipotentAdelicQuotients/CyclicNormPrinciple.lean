import Mathlib

namespace HeckeCharacterZeroLocus

open NumberField IsDedekindDomain

def CyclicNormPrinciple : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    IsGalois F E → IsCyclic (E ≃ₐ[F] E) → ∀ x : F, x ≠ 0 →
    (∀ v : HeightOneSpectrum (𝓞 F), ∃ y : TensorProduct F (v.adicCompletion F) E,
        Algebra.norm (v.adicCompletion F) y = algebraMap F (v.adicCompletion F) x) →
    (∀ σ : F →+* ℝ, (¬ ∃ τ : E →+* ℝ, τ.comp (algebraMap F E) = σ) → 0 < σ x) →
    ∃ y : E, Algebra.norm F y = x

end HeckeCharacterZeroLocus
