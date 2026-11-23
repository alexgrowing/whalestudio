import Mathlib

namespace PI

open NumberField IsDedekindDomain

def AdCpctDen : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (C : Set (FiniteAdeleRing (𝓞 F) F)), IsCompact C →
    ∃ N : ℕ, 0 < N ∧ ∀ f : F, algebraMap F (FiniteAdeleRing (𝓞 F) F) f ∈ C → IsIntegral ℤ ((N : F) * f)

end PI
