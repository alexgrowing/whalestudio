import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVirtualCharacterSemidirectOrbitCrossTerms
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_virtualCharacter_semidirect_orbit_cross_terms : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ a b : G → ℂ, a ∈ Virt ℂ ℂ G → b ∈ Virt ℂ ℂ G → ∃ Z ∈ Virt ℂ ℂ (G ⋊[φ] Γ), (∀ g, Z (inl g) = ∏ t : Γ, (a (φ t g) + b (φ t g)) - ∏ t : Γ, a (φ t g) - ∏ t : Γ, b (φ t g)) ∧ ∀ δ, Z (inl δ * inr s) = 0 := by
  first | (exact @GlobalTheory.CrossOrbit.cross_terms_induced) | (exact GlobalTheory.CrossOrbit.cross_terms_induced) | (intros; apply GlobalTheory.CrossOrbit.cross_terms_induced <;> assumption)
