import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def GenericSectionsInj.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f],
    ∃ m : ℕ, 0 < m ∧ ∀ (k : ℤ) (hk : IsUnit (k : ℚ)), (m : ℤ) ∣ k →
      ∀ W : (invOpen f k : Scheme.{0}).Opens, Function.Injective ((toInvOpen f ℚ k hk).app W)

end

end GroundTheory.Heights₂.Heights.Model
