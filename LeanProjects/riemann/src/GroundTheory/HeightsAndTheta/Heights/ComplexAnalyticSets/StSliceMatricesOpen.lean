import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def SliceMatricesOpen.Statement : Prop :=
  ∀ (n k m : ℕ) (γ : Fin m → (Fin (k + 1) → ℂ) → Fin n → ℂ) (s : Fin m → Fin (k + 1) → ℂ),
    (∀ b, DifferentiableAt ℂ (γ b) (s b)) →
    (∀ b (v : Fin (k + 1) → ℂ), v 0 = 0 → fderiv ℂ (γ b) (s b) v = 0 → v = 0) →
      IsOpen {L : Matrix (Fin k) (Fin n) ℂ |
          ∀ b, Function.Bijective (fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ b t)) (s b))} ∧
        {L : Matrix (Fin k) (Fin n) ℂ |
          ∀ b, Function.Bijective (fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ b t)) (s b))}.Nonempty

end

end GroundTheory.Heights₂.Heights
