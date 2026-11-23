import Mathlib

namespace PI

open Matrix

def PowBddInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (k : ℕ) (γ : Matrix (Fin k) (Fin k) E) (N : ℕ), 0 < N →
    (∀ (n : ℕ) (i j : Fin k), IsIntegral ℤ ((N : E) * (γ ^ n) i j)) →
    ∀ i, IsIntegral ℤ (γ.charpoly.coeff i)

end PI
