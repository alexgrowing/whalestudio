import Mathlib
import Formalism.LocalRingCardinality.DataCoeff

noncomputable section

namespace PI

open Formalism.BasicNotions MvPolynomial

def HwIrred : Prop :=
  ∀ (N : ℕ) (lam : DomWeight N), nablaSq ℂ N lam = delSq ℂ N lam ∧
    (∀ U : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ), U ≤ nablaSq ℂ N lam →
      (∀ (g : GL (Fin N) ℂ), ∀ f ∈ U, sqAct ℂ N lam g f ∈ U) → U = ⊥ ∨ U = nablaSq ℂ N lam) ∧
    ∀ f ∈ nablaSq ℂ N lam,
      (∀ g : GL (Fin N) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) → sqAct ℂ N lam g f = f) →
      ∃ c : ℂ, f = c • extremal ℂ N lam

end PI
