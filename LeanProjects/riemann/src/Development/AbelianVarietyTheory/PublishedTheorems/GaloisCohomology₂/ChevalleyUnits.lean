import Mathlib

open NumberField

namespace GlobalTheory.Published

def ChevalleyUnits : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (m b : ℕ), 0 < m → 0 < b →
    ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 → ∃ v : (𝓞 E)ˣ, u = v ^ m

end GlobalTheory.Published
