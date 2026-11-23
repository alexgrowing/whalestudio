import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

def PullbackFaithful.Statement : Prop :=
  ∀ (T U : Scheme.{u}) (g : T ⟶ U), (∀ W : U.Opens, Function.Injective (g.app W)) →
    ∀ (A B : U.Modules), IsVectorBundle B → ∀ ψ₁ ψ₂ : A ⟶ B,
      (Scheme.Modules.pullback g).map ψ₁ = (Scheme.Modules.pullback g).map ψ₂ → ψ₁ = ψ₂

end

end GroundTheory.Heights₂.Heights.Model
