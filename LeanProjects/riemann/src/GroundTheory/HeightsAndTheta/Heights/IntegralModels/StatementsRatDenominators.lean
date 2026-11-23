import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def RatDenominators.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) (U : X.Opens), IsAffineOpen U →
    ∀ b : Γ(baseChange f ℚ, baseChangeMap f ℚ ⁻¹ᵁ U),
      ∃ N : ℕ, 0 < N ∧ ∃ c : Γ(X, U), (baseChangeMap f ℚ).app U c = N • b

end

end GroundTheory.Heights₂.Heights.Model
