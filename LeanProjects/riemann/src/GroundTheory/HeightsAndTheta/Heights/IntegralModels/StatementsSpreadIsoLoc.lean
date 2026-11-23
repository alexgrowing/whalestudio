import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

def SpreadIsoLoc.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (U : X.Opens) (F G : (U : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ β : (Scheme.Modules.pullback (baseChangeMap f (ZLoc p) ∣_ U)).obj F ≅
      (Scheme.Modules.pullback (baseChangeMap f (ZLoc p) ∣_ U)).obj G,
    ∃ (m : ℕ) (_ : 0 < m) (_ : ¬ (p : ℕ) ∣ m)
      (ψ : (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U ⊓ invOpen f m ≤ U))).obj F ≅
        (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U ⊓ invOpen f m ≤ U))).obj G),
      pullbackIsoAlong (rfl : (baseChangeMap f (ZLoc p) ∣_ (U ⊓ invOpen f m)) ≫
          X.homOfLE (inf_le_left : U ⊓ invOpen f m ≤ U) = _) ψ =
        pullbackIsoAlong (morphismRestrict_homOfLE (baseChangeMap f (ZLoc p)) (U ⊓ invOpen f m) U
          inf_le_left).symm β

end

end GroundTheory.Heights₂.Heights.Model
