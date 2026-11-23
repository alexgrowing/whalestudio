import Mathlib
import Formalism.PeriodIntegrals.SymplZ

namespace PI.SymplZW

open Matrix

abbrev J (k : ℕ) : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℤ :=
  Matrix.fromBlocks 0 1 (-1) 0

def AbsSympl : Prop :=
  ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] (_ : Module.Basis (Fin n) ℤ M)
    (B : M →ₗ[ℤ] M →ₗ[ℤ] ℤ), (∀ x, B x x = 0) → Function.Injective B →
      Function.Surjective B →
      ∃ (k : ℕ) (c : Module.Basis (Fin k ⊕ Fin k) ℤ M), ∀ i j, B (c i) (c j) = J k i j

def MatStep : Prop := AbsSympl → PI.SymplZ

end PI.SymplZW
