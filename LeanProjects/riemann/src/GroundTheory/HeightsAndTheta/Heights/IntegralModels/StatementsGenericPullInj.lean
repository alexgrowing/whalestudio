import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PullbackBasis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def GenericPullInj.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (a : ℕ) (ha : 0 < a)
    (G : (invOpen f a : Scheme.{0}).Modules), IsVectorBundle G →
    ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, 0 < n → m ∣ n →
      ∀ V : (invOpen f a : Scheme.{0}).Opens, V ≤ invOpen ((invOpen f a).ι ≫ f) ((a : ℤ) * n) →
        Function.Injective
          (pullSectionOn (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))) G V)

end

end GroundTheory.Heights₂.Heights.Model
