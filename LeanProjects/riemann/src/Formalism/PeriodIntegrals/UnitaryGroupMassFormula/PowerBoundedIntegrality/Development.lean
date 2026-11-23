import Mathlib
import Formalism.PeriodIntegrals.PowBddInt

namespace PI.PowBddIntWork

open Matrix

def StepA : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (k : ℕ) (γ : Matrix (Fin k) (Fin k) E) (N : ℕ), 0 < N →
    (∀ (n : ℕ) (i j : Fin k), IsIntegral ℤ ((N : E) * (γ ^ n) i j)) → IsIntegral ℤ γ

def StepB : Prop :=
  ∀ (E : Type) [Field E] (k : ℕ) (γ : Matrix (Fin k) (Fin k) E), IsIntegral ℤ γ →
    ∀ i, IsIntegral ℤ (γ.charpoly.coeff i)

theorem powBddInt_of (ha : StepA) (hb : StepB) : PI.PowBddInt := by
  intro E _ _ k γ N hN h i
  exact hb E k γ (ha E k γ N hN h) i

end PI.PowBddIntWork
