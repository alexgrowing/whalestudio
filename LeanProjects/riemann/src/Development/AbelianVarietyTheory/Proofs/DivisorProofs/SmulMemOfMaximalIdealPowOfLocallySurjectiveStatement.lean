import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfMaximalIdealPowOfLocallySurjective
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smul_mem_of_maximalIdeal_pow_of_locally_surjective : ∀ (R B : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup B] [Module R B] [Module.Finite R B] (N : Submodule R B), (∀ (p : Ideal R), p.IsPrime → p ≠ maximalIdeal R → ∀ b : B, ∃ t ∉ p, t • b ∈ N) → ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, x • b ∈ N := by
  first | exact @GlobalTheory.smul_mem_of_maximalIdeal_pow_of_locally_eq | exact GlobalTheory.smul_mem_of_maximalIdeal_pow_of_locally_eq | (intros; apply GlobalTheory.smul_mem_of_maximalIdeal_pow_of_locally_eq <;> assumption)
