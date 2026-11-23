import Mathlib
import Formalism.PeriodIntegrals.UnitaryDense

open Matrix
open scoped ComplexOrder

namespace PI.UD

def SVDStep : Prop :=
  ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), g.det ≠ 0 →
    ∃ (w v : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ),
      wᴴ * w = 1 ∧ vᴴ * v = 1 ∧ g = w * diagonal d * v

def GramStep : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), G.PosDef →
    ∃ C : Matrix (Fin n) (Fin n) ℂ, Cᴴ * C = G ∧ C.det ≠ 0

end PI.UD
