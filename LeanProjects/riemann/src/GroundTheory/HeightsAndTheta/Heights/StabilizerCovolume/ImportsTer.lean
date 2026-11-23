import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.CocycleZeroMemInvariants
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

def UnitaryFirstMinimumPositive.Statement : Prop :=
  ∀ {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] (D : FullerData II Ψ K ι Ω E Em),
    ∀ z ∈ D.Xo, 0 < D.lam1 z

end GroundTheory.Heights₂.Heights.NineStatements
