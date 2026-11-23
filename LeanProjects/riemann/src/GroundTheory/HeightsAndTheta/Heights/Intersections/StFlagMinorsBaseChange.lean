import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

def FlagMinorsBaseChange.Statement : Prop :=
  ∀ (F : Type) [Field F] (n N1 : ℕ) (B : Matrix (Fin n) (Fin N1) F), LinearIndependent F B →
    Algebra.adjoin F (Set.range fun q : Σ j, PluckerBlocks N1 n j => flagMinor (genMat F n * B.map C) q.1 q.2) =
      Algebra.adjoin F (Set.range fun q : Σ j, PluckerBlocks n n j => flagMinor (genMat F n) q.1 q.2)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
