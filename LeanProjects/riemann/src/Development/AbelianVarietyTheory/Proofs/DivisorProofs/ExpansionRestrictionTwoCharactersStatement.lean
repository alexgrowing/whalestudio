import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionRestrictionTwoCharacters
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_polynomial_independent : (∀ (G : Type) [CommGroup G] (L : G → ℝ), (∀ x y, L (x * y) = L x + L y) → (∃ t, L t ≠ 0) → ∀ (ι : Type) [Fintype ι] (χ : ι → G →* ℂˣ), Function.Injective χ → ∀ (P : ι → ℂ[X]), (∀ t, ∑ i, (P i).eval ((L t : ℝ) : ℂ) * ((χ i t : ℂˣ) : ℂ) = 0) → ∀ i, P i = 0) → ∀ (T : Type) [CommGroup T] (L : T → ℝ), (∀ x y, L (x * y) = L x + L y) → ∀ (N : ℕ) (χ : Fin N → T →* ℂˣ) (P : Fin N → ℂ[X]), Function.Injective χ → ∀ (H : Subgroup T) (ψ₁ ψ₂ : T →* ℂˣ), (∃ x ∈ H, L x ≠ 0) → (∀ s, ∃ p q : ℂ, ∀ x ∈ H, ∑ i, (P i).eval ((L (x * s) : ℝ) : ℂ) * ((χ i (x * s) : ℂˣ) : ℂ) = p * ((ψ₁ x : ℂˣ) : ℂ) + q * ((ψ₂ x : ℂˣ) : ℂ)) → ∀ i, P i ≠ 0 → derivative (P i) = 0 ∧ ((∀ x ∈ H, χ i x = ψ₁ x) ∨ ∀ x ∈ H, χ i x = ψ₂ x) := by
  first | exact @GlobalTheory.expansion_restrict_two_characters | exact GlobalTheory.expansion_restrict_two_characters | (intros; apply GlobalTheory.expansion_restrict_two_characters <;> assumption)
