import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

def RatLocalAffine.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [Flat f] (U : X.Opens), IsAffineOpen U →
    Function.Injective ((baseChangeMap f ℚ).app U) ∧
      ∀ b : Γ(baseChange f ℚ, baseChangeMap f ℚ ⁻¹ᵁ U),
        ∃ N : ℕ, 0 < N ∧ ∃ a : Γ(X, U), (baseChangeMap f ℚ).app U a = N • b

end

end GroundTheory.Heights₂.Heights.Model
