import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmulOfForallCharPowEqOne
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_nsmul_of_forall_char_pow_eq_one : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (F : Type) [Field F] [IsAlgClosed F] (k : ℕ), (k : F) ≠ 0 → ∀ d : X, (∀ τ : Multiplicative X →* Fˣ, τ ^ k = 1 → τ (Multiplicative.ofAdd d) = 1) → ∃ z : X, d = k • z := by
  first | exact @GlobalTheory.mem_smul_of_forall_char_pow_eq_one | exact GlobalTheory.mem_smul_of_forall_char_pow_eq_one | (intros; apply GlobalTheory.mem_smul_of_forall_char_pow_eq_one <;> assumption)
