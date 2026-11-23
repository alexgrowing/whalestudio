import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def ProjBundleDim.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (N1 n : ℕ)
    (P : Ideal (MRing ι)) (d : ℕ) (B : Matrix (Fin n) (Fin N1) (FnField P)),
    IsArithVar P d → LinearIndependent (FnField P) B →
    ringKrullDim (MRing (PBlk ι N1) ⧸ projBundleIdeal P B) = ringKrullDim (MRing ι ⧸ P) + (n : WithBot ℕ∞)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
