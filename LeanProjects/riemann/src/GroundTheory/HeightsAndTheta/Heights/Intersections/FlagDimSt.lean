import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def flagIdealOver (F : Type) [Field F] (n : ℕ) : Ideal (MRingOver F (PluckerBlocks n n)) :=
  RingHom.ker (aeval (fun q : Σ j, PluckerBlocks n n j => flagMinor (genMat F n) q.1 q.2) :
    MRingOver F (PluckerBlocks n n) →ₐ[F] MvPolynomial (Fin n × Fin n) F)

theorem flagIdealQ_eq (n : ℕ) : flagIdealQ n = flagIdealOver ℚ n := rfl

theorem flagIdealOver_isPrime (F : Type) [Field F] (n : ℕ) : (flagIdealOver F n).IsPrime :=
  RingHom.ker_isPrime _

def FlagDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ), IsProjVarF (flagIdealOver F n) (flagDim n)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
