import Mathlib

open NumberField

namespace Formalism.L2.SG.Pf.UnipLat

def OEApprox : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 →
    ∀ φ : InfinitePlace F → (E →+* ℂ), (∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) →
    ∃ R : ℝ, ∀ t : InfinitePlace F → ℂ, ∃ y : 𝓞 E, ∀ v, ‖t v - φ v (y : E)‖ ≤ R

end Formalism.L2.SG.Pf.UnipLat
