import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ImportsAlt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def flZIncr (Ψ : Type) (N : ℕ) :
    (Σ q : Ψ × Fin (N - 1), IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FlZBlk Ψ N q) → (Σ q : FlBlock Ψ N, FlIdx Ψ N q) :=
  fun p => ⟨p.1, ⟨p.2.1.orderEmbOfFin p.2.2, (p.2.1.orderEmbOfFin p.2.2).strictMono⟩⟩

def FlZIdealEqCoord.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ),
    IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FlZIdeal Ψ N = mCoordIdeal (fun p => yFl Ψ N (flZIncr Ψ N p))

end GroundTheory.Heights₂.Heights.LowerBoundFree
