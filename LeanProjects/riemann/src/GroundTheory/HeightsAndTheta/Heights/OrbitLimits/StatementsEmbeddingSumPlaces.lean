import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace

def EmbeddingSumPlaces.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (g : (F →+* ℂ) → ℝ),
    (∀ σ, g (ComplexEmbedding.conjugate σ) = g σ) →
      ∑ σ : F →+* ℂ, g σ = ∑ w : InfinitePlace F, (mult w : ℝ) * g w.embedding

end GroundTheory.Heights₂.Heights.Targets
