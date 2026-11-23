import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

def SpreadHomInjLoc.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (U : X.Opens) (F G : (U : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ n : ℕ, 0 < n → m ∣ n → ¬ (p : ℕ) ∣ n →
      ∀ ψ₁ ψ₂ : (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U ⊓ invOpen f n ≤ U))).obj F ⟶
          (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U ⊓ invOpen f n ≤ U))).obj G,
        pullbackHomAlong (rfl : (baseChangeMap f (ZLoc p) ∣_ (U ⊓ invOpen f n)) ≫
            X.homOfLE (inf_le_left : U ⊓ invOpen f n ≤ U) = _) ψ₁ =
          pullbackHomAlong (rfl : (baseChangeMap f (ZLoc p) ∣_ (U ⊓ invOpen f n)) ≫
            X.homOfLE (inf_le_left : U ⊓ invOpen f n ≤ U) = _) ψ₂ →
        ψ₁ = ψ₂

end

end GroundTheory.Heights₂.Heights.Model
