import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ManyIndependentProductsInFunctionField
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearIndependent_products_function_field : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin D → K), IsTranscendenceBasis ℤ x → ∀ (J : Type) [Fintype J] (e : J → K), LinearIndependent ℤ e → ∀ m : ℕ, 0 < m → ∃ v : Fin (Fintype.card J * m ^ D) → K, LinearIndependent ℤ v ∧ ∀ s, ∃ (u : Fin m → J) (a : Fin D → ℕ), (∀ i, a i < m) ∧ v s = (∏ l, e (u l)) * ∏ i, x i ^ a i := by
  first | exact @GlobalTheory.many_independent_products_in_function_field | exact GlobalTheory.many_independent_products_in_function_field | (intros; apply GlobalTheory.many_independent_products_in_function_field <;> assumption)
