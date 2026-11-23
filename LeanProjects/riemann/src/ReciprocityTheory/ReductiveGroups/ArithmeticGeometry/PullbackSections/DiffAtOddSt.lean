import Mathlib

noncomputable section

open NumberField UniqueFactorizationMonoid

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

def DiffExpSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (ℓ a m : ℕ), ℓ.Prime → ¬ ℓ ∣ m →
    (discr E).natAbs = ℓ ^ a * m →
    ∀ P : Ideal (𝓞 E), P.IsPrime → (ℓ : 𝓞 E) ∈ P →
      (normalizedFactors (differentIdeal ℤ (𝓞 E))).count P * Module.finrank ℚ E =
        a * (normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).count P

def DiffAt2St : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (e m : ℕ), Module.finrank ℚ E = 2 ^ (e + 2) → Odd m →
    (discr E).natAbs = 2 ^ (2 ^ (e + 2) * (e + 1) - 4) * m →
    ∀ P : Ideal (𝓞 E), P.IsPrime → (2 : 𝓞 E) ∈ P →
      ((normalizedFactors (differentIdeal ℤ (𝓞 E))).count P : ℝ) /
          ((normalizedFactors (Ideal.span {(2 : 𝓞 E)})).count P : ℝ) = (e : ℝ) + 1 - (2 : ℝ)⁻¹ ^ e

def DiffAtOddSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (e ℓ m : ℕ), ℓ.Prime → Module.finrank ℚ E = 2 ^ (e + 2) →
    ¬ ℓ ∣ m → (discr E).natAbs = ℓ ^ (2 ^ (e + 1)) * m →
    ∀ P : Ideal (𝓞 E), P.IsPrime → (ℓ : 𝓞 E) ∈ P →
      ((normalizedFactors (differentIdeal ℤ (𝓞 E))).count P : ℝ) /
          ((normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).count P : ℝ) = 1 / 2

end ReciprocityTheory.ChartRestriction.G.PullbackSections
