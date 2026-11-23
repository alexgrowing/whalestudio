import Mathlib
import Formalism.PeriodIntegrals.KerIso

noncomputable section
open NumberField

namespace PI.KerIso

def SelfDualOfDiff : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E) (𝔟 𝔟c : Ideal (𝓞 E)),
    IsConj K cj → (∀ x : 𝓞 E, x ∈ 𝔟c ↔ ∃ y ∈ 𝔟, cj (y : E) = (x : E)) →
    differentIdeal (𝓞 K) (𝓞 E) = 𝔟 * 𝔟c →
      SelfDualI K cj ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹)

def SplitOfJacobi : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E) (d p : ℕ) (s : K),
    d % 8 = 7 → s * s = -(d : K) → cj (algebraMap K E s) = -algebraMap K E s → p.Prime →
    (p = 2 ∨ jacobiSym (-(d : ℤ)) p = 1) → SplitsAt K cj p

end PI.KerIso
