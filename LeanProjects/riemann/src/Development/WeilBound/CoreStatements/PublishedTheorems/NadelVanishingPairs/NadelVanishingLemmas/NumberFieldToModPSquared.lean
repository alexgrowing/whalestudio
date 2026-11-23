import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumberFieldToModPSquared
open scoped TensorProduct Polynomial
theorem _root_.GlobalTheory.T.number_field_to_mod_p_squared : ∀ (K : Type) [Field K] [NumberField K] (S : Finset K) (n : ℕ), ∃ p : ℕ, p.Prime ∧ n < p ∧ Nonempty (Subring.closure (S : Set K) →+* ZMod (p ^ 2)) := by
  first | exact @_root_.GlobalTheory.exists_prime_sq_ringHom_of_closure | exact _root_.GlobalTheory.exists_prime_sq_ringHom_of_closure | (intros; apply _root_.GlobalTheory.exists_prime_sq_ringHom_of_closure <;> assumption)
