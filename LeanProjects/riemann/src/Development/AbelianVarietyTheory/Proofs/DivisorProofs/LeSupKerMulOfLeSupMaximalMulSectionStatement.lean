import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSupKerMulOfLeSupMaximalMulSection
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_sup_ker_mul_of_le_sup_maximal_mul_section : ∀ (O P : Type) [CommRing O] [IsLocalRing O] [CommRing P] [Algebra O P] (η : P →ₐ[O] O) (J S : Ideal P), J.FG → J ≤ S ⊔ (IsLocalRing.maximalIdeal O).comap η * J → J ≤ S ⊔ RingHom.ker η * J := by
  first | exact @GlobalTheory.nakayama_at_section | exact GlobalTheory.nakayama_at_section | (intros; apply GlobalTheory.nakayama_at_section <;> assumption)
