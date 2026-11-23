import Mathlib

namespace Formalism.FourierDecayAlt.L

open NumberField

def DualIdealInclusion : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (dd : FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = dd⁻¹ →
    ∀ (ν : ℤ) (g : ℤ), g ≠ 0 → ∀ La : FractionalIdeal (nonZeroDivisors (𝓞 E)) E,
      dd ^ ν * FractionalIdeal.spanSingleton _ ((g : E) ^ 2) ≤ La →
      FractionalIdeal.spanSingleton _ (g : E) * FractionalIdeal.dual ℤ ℚ La ≤
        dd ^ (-(ν + 1)) * FractionalIdeal.spanSingleton _ ((g : E)⁻¹)

def DualLatticeInclusion : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (dd : FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = dd⁻¹ →
    ∀ (ν : ℤ) (g : ℤ), g ≠ 0 → ∀ La : Submodule ℤ E,
      (∀ y ∈ (dd ^ ν * FractionalIdeal.spanSingleton _ ((g : E) ^ 2) :
        FractionalIdeal (nonZeroDivisors (𝓞 E)) E), y ∈ La) →
      ∀ x : E, (∀ y ∈ La, Algebra.trace ℚ E (x * y / g) ∈ (algebraMap ℤ ℚ).range) →
        x ∈ (dd ^ (-(ν + 1)) * FractionalIdeal.spanSingleton _ ((g : E)⁻¹) :
          FractionalIdeal (nonZeroDivisors (𝓞 E)) E)

end Formalism.FourierDecayAlt.L
