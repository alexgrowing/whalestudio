import Mathlib

open NumberField

namespace UpperTheory.V.Published

def FerreroWashington : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K],
    (∃ ζ : K, IsPrimitiveRoot ζ (if l = 2 then 4 else l)) →
    ∃ r : ℕ, ∀ (n : ℕ) (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] [IsCyclotomicExtension {l ^ n} K K'],
      Nat.card (ClassGroup (𝓞 K') ⧸ (powMonoidHom l : ClassGroup (𝓞 K') →* ClassGroup (𝓞 K')).range) ≤ l ^ r

end UpperTheory.V.Published
