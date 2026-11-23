import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeFormIdealDualVectorIntegral
import Mathlib
open NumberField
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_form_ideal_dual_vector_integral : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V], Module.finrank F V = 2 → ∀ (B : LinearMap.BilinForm F V), (∀ z, B z z = 0) → ∀ (L : Set V), (0 : V) ∈ L → (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) → (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) →
    ∀ (J : FractionalIdeal (𝓞 F)⁰ F), J ≠ 0 → (∀ z ∈ L, ∀ w ∈ L, B z w ∈ J) →
    (∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}) →
    ∀ {v : V}, v ≠ 0 → ∃ I : FractionalIdeal (𝓞 F)⁰ F, I ≠ 0 ∧ ∀ a : F, a ∈ I ↔ a • v ∈ L := by
  first | exact @GlobalTheory.exists_fractionalIdeal_smul_mem_lattice_of_alternating | exact GlobalTheory.exists_fractionalIdeal_smul_mem_lattice_of_alternating | (intros; apply GlobalTheory.exists_fractionalIdeal_smul_mem_lattice_of_alternating <;> assumption)
