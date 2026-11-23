import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatLiftModPSqPerfectField
import Mathlib
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flat_lift_mod_p_sq_perfect_field : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectField k], ∃ (Λ : Type) (_ : CommRing Λ) (π : Λ →+* k), Function.Surjective π ∧ RingHom.ker π = Ideal.span {(p : Λ)} ∧ (p : Λ) ^ 2 = 0 ∧ ∀ x : Λ, (p : Λ) * x = 0 → x ∈ Ideal.span {(p : Λ)} := by
  first | exact @GlobalTheory.exists_flat_lift_mod_p_sq | exact GlobalTheory.exists_flat_lift_mod_p_sq | (intros; apply GlobalTheory.exists_flat_lift_mod_p_sq <;> assumption)
