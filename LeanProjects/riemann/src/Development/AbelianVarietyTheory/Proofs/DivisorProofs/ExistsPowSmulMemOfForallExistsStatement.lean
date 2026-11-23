import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulMemOfForallExists
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_smul_mem_of_forall_exists' : ∀ (S : Type) [CommRing S] (I : Ideal S) (M : Type) [AddCommGroup M] [Module S M] [Module.Finite S M] (N : Submodule S M), (∀ y : M, ∃ k : ℕ, ∀ a ∈ I ^ k, a • y ∈ N) → ∃ k : ℕ, ∀ a ∈ I ^ k, ∀ y : M, a • y ∈ N := by
  first | exact @GlobalTheory.Submodule.exists_pow_smul_mem_of_forall_exists | exact GlobalTheory.Submodule.exists_pow_smul_mem_of_forall_exists | (intros; apply GlobalTheory.Submodule.exists_pow_smul_mem_of_forall_exists <;> assumption)
