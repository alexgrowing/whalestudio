import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.GenericMinors
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def PlueckerSpan.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (τ : Ψ) (i : Fin (D.N - 1)),
    Submodule.span Ω (Set.range (Pl.pluecker τ i)) =
      Submodule.span Ω (Set.range (flagMinor (genMatFr Ω Ψ D.N τ) i))

end GroundTheory.Heights₂.Heights.LowerBoundFree
