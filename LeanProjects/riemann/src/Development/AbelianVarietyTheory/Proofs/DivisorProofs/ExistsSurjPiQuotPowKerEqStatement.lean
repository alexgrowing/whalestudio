import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjPiQuotPowKerEq
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_surjective_pi_quotient_pow_ker_eq : ∀ {A M : Type} [CommRing A] [IsDedekindDomain A] [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M] (P : Ideal A), P.IsMaximal → ∀ (r d : ℕ), Module.finrank A M = d → ∃ g : M →ₗ[A] (Fin d → A ⧸ P ^ r), Function.Surjective g ∧ ∀ x, g x = 0 ↔ x ∈ (P ^ r) • (⊤ : Submodule A M) := by
  first | (exact @GlobalTheory.exists_surj_pi_quot_pow_ker_eq) | (exact GlobalTheory.exists_surj_pi_quot_pow_ker_eq) | (intros; apply GlobalTheory.exists_surj_pi_quot_pow_ker_eq  <;> assumption)
