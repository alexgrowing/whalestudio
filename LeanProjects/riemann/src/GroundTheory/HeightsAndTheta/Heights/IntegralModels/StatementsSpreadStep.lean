import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

def SpreadStep.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (E : (baseChange f (ZLoc p)).Modules) (W₁ W₂ : X.Opens),
    SpreadsOn f (ZLoc p) E W₁ → SpreadsOn f (ZLoc p) E W₂ →
    ∃ W : X.Opens, baseChangeMap f (ZLoc p) ⁻¹ᵁ W₁ ⊔ baseChangeMap f (ZLoc p) ⁻¹ᵁ W₂ ≤
        baseChangeMap f (ZLoc p) ⁻¹ᵁ W ∧ SpreadsOn f (ZLoc p) E W

end

end GroundTheory.Heights₂.Heights.Model
