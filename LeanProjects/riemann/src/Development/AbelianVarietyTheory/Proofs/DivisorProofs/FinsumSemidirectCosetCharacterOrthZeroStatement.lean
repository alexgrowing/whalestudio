import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumSemidirectCosetCharacterOrthZero
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_semidirect_coset_character_orth_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X Y : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ X → IsChar ℂ ℂ Y → ∑ᶠ g, X (inl g) * star (Y (inl g)) = 0 → ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = 0 := by
  first | (exact @GlobalTheory.Shin.finsum_coset_mul_star_eq_zero) | (exact GlobalTheory.Shin.finsum_coset_mul_star_eq_zero) | (intros; apply GlobalTheory.Shin.finsum_coset_mul_star_eq_zero <;> assumption)
