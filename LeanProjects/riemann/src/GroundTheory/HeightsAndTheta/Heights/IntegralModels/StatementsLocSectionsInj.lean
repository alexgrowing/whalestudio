import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def LocSectionsInj.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes),
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ k : ℤ, ¬ ((p : ℕ) : ℤ) ∣ k → (m : ℤ) ∣ k →
      ∀ W : X.Opens, W ≤ invOpen f k →
        Function.Injective ((baseChangeMap f (ZLoc p)).app W)

end

end GroundTheory.Heights₂.Heights.Model
