import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.CocycleZeroMemInvariants
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

def UnitaryIsotropicRank.Statement : Prop :=
  ∀ {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}
    (A : HermDatum Em Ψ N j) (I : Submodule (𝓞 Em) (Fin N → Em)), A.IsIso I →
      ∀ (ρ : ℕ) (v : Fin ρ → Fin N → Em), IsNzFamily I ρ v → ρ ≤ N - j

end GroundTheory.Heights₂.Heights.NineStatements
