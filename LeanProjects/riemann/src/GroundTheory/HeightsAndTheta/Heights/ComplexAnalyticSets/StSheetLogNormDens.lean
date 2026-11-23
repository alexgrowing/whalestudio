import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def SheetLogNormDens.Statement : Prop :=
  ∀ (n d m : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (x : Fin n → ℂ)
    (s : (Fin d → ℂ) → Fin n → ℂ) (T : Fin d → Matrix (Fin m) (Fin n) ℂ),
    IsSheetAt J A x s → (∀ k, T k *ᵥ x ≠ 0) →
      0 ≤ ReciprocityTheory.AnForm.maDens
        (fun k => (fun z => Real.log √(∑ i, ‖(T k *ᵥ z) i‖ ^ 2)) ∘ s) (A *ᵥ x)

end

end GroundTheory.Heights₂.Heights
