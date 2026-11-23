import Mathlib
import Formalism.PeriodIntegrals.Minkowski

namespace PI.Mk

open Matrix

def TraceStep : Prop :=
  ∀ (N ℓ a : ℕ), ℓ.Prime → ∀ g : Matrix (Fin N) (Fin N) ℤ, g ^ (ℓ ^ a) = 1 →
    ∃ y : ℕ, y ≤ N / (ℓ - 1) ∧ g.trace = (N : ℤ) - (ℓ : ℤ) * (y : ℤ) ∧ (y = 0 → g = 1)

def PowerSumStep : Prop :=
  ∀ (N : ℕ) (P : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℤ)) [Fintype P] (k : ℕ),
    (Fintype.card P : ℤ) ∣ ∑ g : P, (Matrix.trace ((g : Matrix.GeneralLinearGroup (Fin N) ℤ) :
      Matrix (Fin N) (Fin N) ℤ)) ^ k

def PGroupStep : Prop :=
  ∀ (N ℓ : ℕ), ℓ.Prime → ∀ P : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℤ), Finite P →
    IsPGroup ℓ P → Nat.card P ∣ ℓ ^ (N / (ℓ - 1)) * (N / (ℓ - 1)).factorial

end PI.Mk
