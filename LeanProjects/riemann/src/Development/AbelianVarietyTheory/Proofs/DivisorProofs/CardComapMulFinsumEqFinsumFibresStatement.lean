import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardComapMulFinsumEqFinsumFibres
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_comap_mul_finsum_eq_finsum_fibres : ∀ (G₀ G : Type) [Group G₀] [Group G] [Finite G₀] [Finite G] (ι : G₀ →* G) (H : Subgroup G) (T : G → ℂ), (∀ y, T y ≠ 0 → ∃ k p, p ∈ H ∧ y = ι k * p) → (Nat.card (H.comap ι) : ℂ) * ∑ᶠ y, T y = ∑ᶠ k : G₀, ∑ᶠ p : H, T (ι k * p) := by
  first | (exact @GlobalTheory.fibre_count_comap_mul) | (exact GlobalTheory.fibre_count_comap_mul) | (intros; apply GlobalTheory.fibre_count_comap_mul <;> assumption)
