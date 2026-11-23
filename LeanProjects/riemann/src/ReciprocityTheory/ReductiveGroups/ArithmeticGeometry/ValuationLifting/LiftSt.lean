import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.Lift

def ApproxStatement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι : Type) [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))),
    (∀ i, ∃ x, v i x = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
    (∀ i j, i ≠ j → ¬ (v i).IsEquiv (v j)) → ∀ n : ι → ℤ,
      ∃ x : Ω, ∀ i, v i x = ((Multiplicative.ofAdd (n i) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))

end ReciprocityTheory.ChartRestriction.G.Lift
