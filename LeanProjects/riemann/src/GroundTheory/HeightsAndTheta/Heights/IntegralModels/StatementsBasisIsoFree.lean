import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsFreeSheafBasis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

def BasisIsoFree.Statement : Prop :=
  ∀ (Y : Scheme.{u}) (M : Y.Modules) (n : ℕ) (s : Fin n → Γ(M, ⊤)), IsBasisOn M ⊤ s →
    Nonempty (M ≅ freeModule Y n)

end

end GroundTheory.Heights₂.Heights.Model
