import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerRowOperatorMemDualWeylEndSubalgebra
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerRowOperator_mem_dualWeylEndSubalgebra : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (a b : Fin N), a ≠ b → ∀ k : ℕ, ∃ p ∈ dwAlg O N ν, ∀ f : dualWeyl O N N ν, (p f : MvPolynomial (Fin N × Fin N) O) = rowDiv O a b k (f : MvPolynomial (Fin N × Fin N) O) := by
  first | exact @GlobalTheory.GenCoef.rowDiv_mem_dwAlg | exact GlobalTheory.GenCoef.rowDiv_mem_dwAlg | (intros; apply GlobalTheory.GenCoef.rowDiv_mem_dwAlg <;> assumption)
