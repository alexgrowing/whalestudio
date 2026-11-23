import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVectorPairingOneIdealMultiple
import Mathlib
open NumberField
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_vector_pairing_one_ideal_multiple : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V) (L : Set V), (0 : V) ∈ L → (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) →
    (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) → ∀ {v : V} (K : FractionalIdeal (𝓞 F)⁰ F), K ≠ 0 →
    (∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v) → ∃ w : V, B w v = 1 ∧ ∀ t ∈ K, t • w ∈ L := by
  first | exact @GlobalTheory.exists_section_of_fractionalIdeal_values | exact GlobalTheory.exists_section_of_fractionalIdeal_values | (intros; apply GlobalTheory.exists_section_of_fractionalIdeal_values <;> assumption)
