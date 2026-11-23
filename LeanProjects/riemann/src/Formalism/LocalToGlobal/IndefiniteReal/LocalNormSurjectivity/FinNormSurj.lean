import Mathlib

namespace Formalism.IndefR.LocBrg

def FinNormSurj : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (τ : k →+* k), (∀ x, τ (τ x) = x) → (∃ x, τ x ≠ x) →
    ∀ c : k, τ c = c → c ≠ 0 → ∃ x : k, τ x * x = c

def HenselSqrt : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L],
    Valued.v (2 : L) = 1 → ∀ u : L, Valued.v (u - 1) < 1 → ∃ s : L, s * s = u ∧ Valued.v (s - 1) < 1

end Formalism.IndefR.LocBrg
