import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PlueckerCoordinates.IsHodgeFibrePt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PlueckerCoordinates.MuLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

def HodgeFibrePtNeZero.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (P : PlueckerData D) (τ : Ψ)
    (z : (Σ k, ι k) → ℂ) (wF : Fin (P.M τ (jIdx D)) → ℂ) (wW : Fin (P.M τ (lastIdx D)) → ℂ),
    z ∈ mcPts (mCoordIdeal D.y) → IsHodgeFibrePt P τ z wF wW → (∃ m, wF m ≠ 0) ∧ ∃ m, wW m ≠ 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
