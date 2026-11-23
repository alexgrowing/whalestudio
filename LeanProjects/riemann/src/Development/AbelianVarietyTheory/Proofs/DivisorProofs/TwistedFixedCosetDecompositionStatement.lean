import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFixedCosetDecomposition
import Mathlib
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_fixed_coset_decomposition : ∀ {H : Type} [Group H] (Z U : Subgroup H) (τ : H →* H) (r : ℕ), 0 < r → (∀ z ∈ Z, τ z ∈ Z) →
    (∀ z ∈ Z, (⇑τ)^[r] z = z) → (∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) → U ≤ Z → (∀ u ∈ U, τ u ∈ U) →
    (∃ G : Finset H, (∀ g ∈ G, g ∈ Z) ∧ Z ≤ Subgroup.closure ((G : Set H) ∪ (U : Set H))) →
    ∀ F : Finset H, ∃ S : Finset H, ∀ t ∈ Z, (∃ f ∈ F, ∃ u ∈ U, t⁻¹ * τ t = f * u) →
      ∃ b ∈ Z, τ b = b ∧ ∃ s ∈ S, ∃ u ∈ U, t = b * s * u := by
  first | (exact @GlobalTheory.TwLangAb.exists_finite_reps_of_twisted_lang) | (exact GlobalTheory.TwLangAb.exists_finite_reps_of_twisted_lang) | (intros; apply GlobalTheory.TwLangAb.exists_finite_reps_of_twisted_lang <;> assumption)
