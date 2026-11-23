import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorInductionVirtualCharacterPrime
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorInduction_virtualCharacter_prime : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ χ ∈ Virt ℂ ℂ G, ∃ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), (∀ g, X (inl g) = ∏ t : Γ, χ (φ t g)) ∧ ∀ δ, X (inl δ * inr s) = χ (nrmG φ s (Nat.card Γ) δ) := by
  first | (exact @GlobalTheory.Shin.tensorInd_virt_prime) | (exact GlobalTheory.Shin.tensorInd_virt_prime) | (intros; apply GlobalTheory.Shin.tensorInd_virt_prime <;> assumption)
