import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMapLeMapMulKerOfFlatTarget
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_inf_map_le_map_mul_ker_of_flat_target : ∀ (B P A : Type) [CommRing B] [CommRing P] [CommRing A] [Algebra B P] [Algebra B A] [Module.Flat B A] (Ψ : P →ₐ[B] A), Function.Surjective Ψ → ∀ I : Ideal B, RingHom.ker Ψ ⊓ I.map (algebraMap B P) ≤ I.map (algebraMap B P) * RingHom.ker Ψ := by
  first | exact @GlobalTheory.ker_inf_map_le_map_mul_ker_of_flat | exact GlobalTheory.ker_inf_map_le_map_mul_ker_of_flat | (intros; apply GlobalTheory.ker_inf_map_le_map_mul_ker_of_flat <;> assumption)
