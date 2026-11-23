import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagMinorTrdeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def GenLeadMinor0NeZero.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (τ : Ψ) (a : Fin (n - 1)), leadMinor (genMat0Fr F Ψ n j τ) a ≠ 0

end GroundTheory.Heights₂.Heights.LowerBoundFree
