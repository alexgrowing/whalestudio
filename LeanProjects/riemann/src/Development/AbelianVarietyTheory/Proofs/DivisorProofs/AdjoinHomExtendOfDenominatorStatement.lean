import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinHomExtendOfDenominator
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_adjoin_algHom_of_mul_mem_of_map_ne_zero : ∀ (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω] [Algebra k Ω] (S : Subalgebra k F) (ψ : S →ₐ[k] Ω) (h : S), ψ h ≠ 0 → ∀ T : Set F, (∀ x ∈ T, (h : F) * x ∈ S) → Nonempty (Algebra.adjoin k T →ₐ[k] Ω) := by
  first | exact @GlobalTheory.adjoin_hom_extend_of_denominator | exact GlobalTheory.adjoin_hom_extend_of_denominator | (intros; apply GlobalTheory.adjoin_hom_extend_of_denominator <;> assumption)
