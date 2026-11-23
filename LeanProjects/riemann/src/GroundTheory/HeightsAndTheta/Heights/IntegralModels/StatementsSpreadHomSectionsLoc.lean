import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PullbackBasis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def SpreadHomSectionsLoc.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (U : X.Opens) (F G : (U : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ φ : (Scheme.Modules.pullback (baseChangeMap f (ZLoc p) ∣_ U)).obj F ⟶
      (Scheme.Modules.pullback (baseChangeMap f (ZLoc p) ∣_ U)).obj G,
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ n : ℕ, 0 < n → m ∣ n → ¬ (p : ℕ) ∣ n →
      ∀ V : (U : Scheme.{0}).Opens, V ≤ invOpen (U.ι ≫ f) n →
        ∀ s : Γ(F, V), ∃ t : Γ(G, V),
          pullSectionOn (baseChangeMap f (ZLoc p) ∣_ U) G V t =
            φ.app ((baseChangeMap f (ZLoc p) ∣_ U) ⁻¹ᵁ V)
              (pullSectionOn (baseChangeMap f (ZLoc p) ∣_ U) F V s)

end

end GroundTheory.Heights₂.Heights.Model
