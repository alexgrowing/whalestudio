import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPositiveBlockColumnEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
open Matrix Finset Formalism.MainNotions.S Formalism.REAL GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_positiveBlock_column_eq : ∀ (m : ℕ) (ε : Fin m → Bool) (z : Fin m) (u : Fin m → ℂ), ε z = true → (∀ i, ε i = false → u i = 0) → ∑ i, ‖u i‖ ^ 2 = 1 → ∃ k ∈ UJset ε, kᴴ * k = 1 ∧ ∀ i, k i z = u i := by
  first | exact @GlobalTheory.Twist.Boost.exists_unitary_col | exact GlobalTheory.Twist.Boost.exists_unitary_col | (intros; apply GlobalTheory.Twist.Boost.exists_unitary_col <;> assumption)
