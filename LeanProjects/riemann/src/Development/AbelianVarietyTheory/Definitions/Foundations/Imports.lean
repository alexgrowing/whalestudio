import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CthFac

noncomputable section

open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.Sieg

def th (z : ℂ) (τ : ℍ) : ℂ :=
  ee ((τ : ℂ) / 12) * (ee (z / 2) - ee (-z / 2)) *
    ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹)

def act (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : Fin 2 → ℚ := fun i => ∑ j, x j * (((γ : Matrix (Fin 2) (Fin 2) ℤ) j i : ℤ) : ℚ)

end GlobalTheory.Sieg
