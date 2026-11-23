import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PullbackBasis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def PullInjLoc.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (U : X.Opens) (G : (U : Scheme.{0}).Modules), IsVectorBundle G →
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ n : ℕ, 0 < n → m ∣ n → ¬ (p : ℕ) ∣ n →
      ∀ V : (U : Scheme.{0}).Opens, V ≤ invOpen (U.ι ≫ f) n →
        Function.Injective (pullSectionOn (baseChangeMap f (ZLoc p) ∣_ U) G V)

end

end GroundTheory.Heights₂.Heights.Model
