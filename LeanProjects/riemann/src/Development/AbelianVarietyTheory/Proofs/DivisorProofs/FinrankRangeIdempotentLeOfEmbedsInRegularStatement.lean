import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeIdempotentLeOfEmbedsInRegular
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_range_idempotent_le_of_embedsInRegular : ∀ (K Γ V : Type) [Field K] [CharZero K] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] (ρ : Representation K Γ V) (H : Subgroup Γ) (n : ℕ), EmbReg ρ H n → ∀ a : MonoidAlgebra K Γ, (∀ g, a.coeff g ≠ 0 → g ∈ H) → a * a = a → ∃ r : ℕ, (r : K) = (Nat.card H : K) * a.coeff 1 ∧ finrank K (LinearMap.range (ρ.asAlgebraHom a)) ≤ n * r := by
  first | exact @GlobalTheory.BadCount.finrank_range_idem_le_of_embReg | exact GlobalTheory.BadCount.finrank_range_idem_le_of_embReg | (intros; apply GlobalTheory.BadCount.finrank_range_idem_le_of_embReg <;> assumption)
