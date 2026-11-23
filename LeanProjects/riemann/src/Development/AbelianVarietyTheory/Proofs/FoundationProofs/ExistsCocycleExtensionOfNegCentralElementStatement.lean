import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCocycleExtensionOfNegCentralElement
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocycle_extension_of_neg_central_element : ∀ (G : Type) [Group G] (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (ρ : G → V →ₗ[R] V), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → IsUnit (2 : R) → ∀ (S : Submodule R V), (∀ g, ∀ v ∈ S, ρ g v ∈ S) → ∀ (Δ : Subgroup G), Δ.Normal → (∀ δ ∈ Δ, ∀ v, ρ δ v = v) → ∀ c : G, (∀ v ∈ S, ρ c v = -v) → (∀ g, c * g * c⁻¹ * g⁻¹ ∈ Δ) → ∀ φ : G → V, (∀ δ ∈ Δ, φ δ ∈ S) → (∀ δ ∈ Δ, ∀ δ' ∈ Δ, φ (δ * δ') = φ δ + φ δ') → (∀ g, ∀ δ ∈ Δ, ρ g (φ (g * δ * g⁻¹)) = φ δ) → ∃ z : G → V, (∀ g, z g ∈ S) ∧ (∀ g h, z (g * h) = ρ h (z g) + z h) ∧ ∀ δ ∈ Δ, z δ = φ δ := by
  first | exact @GlobalTheory.KZ.H3.exists_cocycle_extension_of_neg_action | exact GlobalTheory.KZ.H3.exists_cocycle_extension_of_neg_action | (intros; apply GlobalTheory.KZ.H3.exists_cocycle_extension_of_neg_action <;> assumption)
