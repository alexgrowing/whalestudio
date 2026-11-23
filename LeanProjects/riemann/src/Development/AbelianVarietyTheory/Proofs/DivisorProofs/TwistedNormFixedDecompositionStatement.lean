import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormFixedDecomposition
import Mathlib
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_norm_fixed_decomposition : ∀ {H : Type} [Group H] (θ : H →* H) (K₀ : Subgroup H) (δ : H) (r : ℕ), 0 < r → (∀ h, (⇑θ)^[r] h = h) →
    (∀ k ∈ K₀, θ k ∈ K₀) → (∀ g : H, Subgroup.Commensurable (K₀.map (MulAut.conj g).toMonoidHom) K₀) →
    ∀ Z : Subgroup H, (∀ z ∈ Z, δ * θ z * δ⁻¹ ∈ Z) → (∀ z ∈ Z, (⇑((MulAut.conj δ).toMonoidHom.comp θ))^[r] z = z) →
    (∃ G : Finset H, (∀ g ∈ G, g ∈ Z) ∧ Z ≤ Subgroup.closure ((G : Set H) ∪ ((Z ⊓ K₀ : Subgroup H) : Set H))) →
    ∃ U : Subgroup H, U ≤ Z ∧ U ≤ K₀ ∧ (∀ u ∈ U, δ * θ u * δ⁻¹ ∈ U) ∧
      (∃ G : Finset H, (∀ g ∈ G, g ∈ Z) ∧ Z ≤ Subgroup.closure ((G : Set H) ∪ (U : Set H))) ∧
      (∀ h g : H, ∃ F : Finset H, ∀ z ∈ Z, ∀ k ∈ K₀, z = h * k * g → ∃ f ∈ F, ∃ u ∈ U, z = f * u) := by
  first | (exact @GlobalTheory.TwistStab.stable_subgroup) | (exact GlobalTheory.TwistStab.stable_subgroup) | (intros; apply GlobalTheory.TwistStab.stable_subgroup  <;> assumption)
