import Mathlib
import GroundTheory.HeightsAndTheta.Heights.QuadraticFields.SqfField
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Rows

def SqfZetaFactor.Statement : Prop :=
  ∀ (d : ℕ) [NeZero d], Squarefree d → d % 4 = 3 →
    ∀ χ : DirichletCharacter ℂ d, (∀ k : ℕ, χ k = ((jacobiSym k d : ℤ) : ℂ)) →
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → (∃ x : K, x ^ 2 = -(d : K)) →
      ∀ s : ℂ, 1 < s.re →
        NumberField.dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction χ s

end GroundTheory.Heights₂.Heights.Rows
