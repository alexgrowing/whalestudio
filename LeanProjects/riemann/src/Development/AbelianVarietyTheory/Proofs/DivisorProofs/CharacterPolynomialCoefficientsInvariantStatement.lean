import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterPolynomialCoefficientsInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_polynomial_coefficients_invariant : ∀ (T : Type) [CommGroup T] (L : T → ℝ), (∀ x y, L (x * y) = L x + L y) → (∃ t, L t ≠ 0) → ∀ (N K : ℕ) (χ : Fin N → T →* ℂˣ) (c : Fin N → Fin (K + 1) → ℂ), Function.Injective χ → ∀ Φ : T → ℂ, (∀ t, Φ t = ∑ i, ∑ k, c i k * ((χ i t : ℂˣ) : ℂ) * ((L t : ℝ) : ℂ) ^ (k : ℕ)) → (∀ γ, L γ = 0 → (∀ t, Φ (γ * t) = Φ t) → ∀ i k, c i k ≠ 0 → χ i γ = 1) ∧ (∀ i k, c i k ≠ 0 → ∃ (n : ℕ) (s : Fin n → T) (b : Fin n → ℂ), ∀ t, ((χ i t : ℂˣ) : ℂ) = ∑ j, b j * Φ (s j * t)) ∧ ∀ (H : Subgroup T) (ψ₁ ψ₂ : T →* ℂˣ), (∃ x ∈ H, L x ≠ 0) → (∀ s, ∃ p q : ℂ, ∀ x ∈ H, Φ (x * s) = p * ((ψ₁ x : ℂˣ) : ℂ) + q * ((ψ₂ x : ℂˣ) : ℂ)) → ∀ i k, c i k ≠ 0 → (k : ℕ) = 0 ∧ ((∀ x ∈ H, χ i x = ψ₁ x) ∨ ∀ x ∈ H, χ i x = ψ₂ x) := by
  first | exact @GlobalTheory.CharPowExp.charPow_expansion | exact GlobalTheory.CharPowExp.charPow_expansion | (intros; apply GlobalTheory.CharPowExp.charPow_expansion <;> assumption)
