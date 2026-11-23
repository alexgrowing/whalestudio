import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectCosetPairingEqZeroOrTwist
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semidirect_coset_pairing_eq_zero_or_twist : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ χ χ' : G ⋊[φ] Γ → ℂ, IsIrrChar ℂ ℂ χ → IsIrrChar ℂ ℂ χ' → ∑ᶠ g, χ (inl g * inr s) * star (χ' (inl g * inr s)) = 0 ∨ ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ ∀ x, χ x = χ' x * (η x : ℂ) := by
  first | (exact @GlobalTheory.Shin.coset_pair_eq_zero_or_twist) | (exact GlobalTheory.Shin.coset_pair_eq_zero_or_twist) | (intros; apply GlobalTheory.Shin.coset_pair_eq_zero_or_twist <;> assumption)
