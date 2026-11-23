import Mathlib
import Formalism.PeriodIntegrals.Minkowski

namespace PI

def FiniteConjIntegral : Prop :=
  ∀ (N : ℕ) (G : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℚ)), Finite G →
    ∃ P : Matrix.GeneralLinearGroup (Fin N) ℚ, ∀ g ∈ G, ∃ h : Matrix.GeneralLinearGroup (Fin N) ℤ,
      P * g * P⁻¹ = Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) h

def MinkowskiBoundQ : Prop :=
  ∀ (N : ℕ) (G : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℚ)), Finite G →
    Nat.card G ∣ minkowskiM N

end PI
