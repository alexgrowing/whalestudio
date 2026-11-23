import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosMulExtendIntLinearForm
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_mul_extend_int_linearForm' : ∀ (F : Type) [AddCommGroup F] [Module.Free ℤ F] [Module.Finite ℤ F] (P : Submodule ℤ F) (f : P →ₗ[ℤ] ℤ), ∃ c : ℤ, 0 < c ∧ ∃ lam : F →ₗ[ℤ] ℤ, ∀ x : P, lam x = c * f x := by
  first | exact @GlobalTheory.exists_pos_mul_extend_int_linearForm | exact GlobalTheory.exists_pos_mul_extend_int_linearForm | (intros; apply GlobalTheory.exists_pos_mul_extend_int_linearForm <;> assumption)
