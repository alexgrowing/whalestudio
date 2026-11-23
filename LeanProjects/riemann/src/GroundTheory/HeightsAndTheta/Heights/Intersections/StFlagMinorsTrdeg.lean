import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

def FlagMinorsTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ),
    Algebra.trdeg F (Algebra.adjoin F (Set.range fun q : Σ j, PluckerBlocks n n j => flagMinor (genMat F n) q.1 q.2)) =
      ((flagDim n + (n - 1) : ℕ) : Cardinal)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
