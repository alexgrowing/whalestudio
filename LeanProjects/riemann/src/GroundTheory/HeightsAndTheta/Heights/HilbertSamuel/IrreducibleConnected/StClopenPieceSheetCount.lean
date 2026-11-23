import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Matrix

def ClopenPieceSheetCount.Statement : Prop :=
  ∀ (n d N : ℕ) (A : Matrix (Fin d) (Fin n) ℂ) (Z : Set (Fin n → ℂ)) (Ω : Set (Fin d → ℂ))
    (O F : Set (Fin n → ℂ)),
    IsOpen Ω → IsPreconnected Ω →
    (∀ y ∈ Ω, {x | x ∈ Z ∧ A *ᵥ x = y}.Finite ∧ {x | x ∈ Z ∧ A *ᵥ x = y}.ncard = N ∧
      ∀ x ∈ Z, A *ᵥ x = y → ∃ (U : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
        (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧
          ContinuousOn g U ∧ g y = x ∧ (∀ w ∈ U, A *ᵥ g w = w) ∧ Z ∩ V = g '' U) →
    IsOpen O → IsClosed F →
    {x | x ∈ Z ∧ A *ᵥ x ∈ Ω} ∩ O = {x | x ∈ Z ∧ A *ᵥ x ∈ Ω} ∩ F →
    ∃ k : ℕ, ∀ y ∈ Ω, {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y}.ncard = k

end GroundTheory.Heights₂.Heights.HilbertSamuel
