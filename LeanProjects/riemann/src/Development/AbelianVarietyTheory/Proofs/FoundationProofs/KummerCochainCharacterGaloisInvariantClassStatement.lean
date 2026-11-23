import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainCharacterGaloisInvariantClass
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_cochain_character_galoisInvariant_class : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 →
  α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b → ∀ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η →
  (∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g) →
  ∃ θ : Ω, θ ≠ 0 ∧ θ ^ N ∈ IntermediateField.adjoin K {α, β} ∧
    (∀ g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup, η g = kum ζ θ g) ∧
    ∀ s : Ω ≃ₐ[K] Ω, ∃ u ∈ IntermediateField.adjoin K {α, β}, u ≠ 0 ∧ s (θ ^ N) = θ ^ N * u ^ N := by
  first | exact @GlobalTheory.eta_kummer_galoisInvariant | exact GlobalTheory.eta_kummer_galoisInvariant | (intros; apply GlobalTheory.eta_kummer_galoisInvariant <;> assumption)
