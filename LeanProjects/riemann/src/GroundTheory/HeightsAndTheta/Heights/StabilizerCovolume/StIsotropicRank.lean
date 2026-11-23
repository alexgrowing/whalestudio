import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.HodgeLength
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField
open scoped Matrix

def IsotropicRank.Statement : Prop :=
  ∀ (Em : Type) [Field Em] [NumberField Em] [IsCMField Em] (Ψ : Type) [Fintype Ψ] (N j : ℕ)
    (A : HermDatum Em Ψ N j) (S : Set (Fin N → Em)),
      (∀ v ∈ S, ∀ w ∈ S, hermForm Em A.H v w = 0) → Module.finrank Em (Submodule.span Em S) ≤ N - j

end GroundTheory.Heights₂.Heights.NineStatements
