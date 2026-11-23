import Mathlib

noncomputable section

namespace PI

open NumberField IntermediateField

def QuadDiff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (d : ℕ) (θ : E), Squarefree d → d % 4 = 3 →
    θ ^ 2 = -(d : E) →
    (((differentIdeal ℤ (𝓞 ℚ⟮θ⟯)).map (algebraMap (𝓞 ℚ⟮θ⟯) (𝓞 E)) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) θ

end PI

end
