import Mathlib

namespace Formalism.MainNotions.S

open NumberField

def SplitsCompl (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : 𝓞 E) ∈ P) → Ideal.absNorm P = p ∧ (p : 𝓞 E) ∉ P ^ 2

end Formalism.MainNotions.S
