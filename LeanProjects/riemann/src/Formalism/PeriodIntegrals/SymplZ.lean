import Mathlib

namespace PI

open Matrix

def SymplZ : Prop :=
  ∀ (n : ℕ) (E : Matrix (Fin n) (Fin n) ℤ), Eᵀ = -E → IsUnit E.det →
    ∃ (k : ℕ) (e : Fin n ≃ Fin k ⊕ Fin k) (P : Matrix (Fin n) (Fin n) ℤ), IsUnit P.det ∧
      P * E * Pᵀ = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 0 1 (-1) 0)

end PI
