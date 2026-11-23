import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsScaledFSTopPos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def ScaledFSHProps.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)),
    IsSemipositiveRel P0 P (scaledFSH ι) ∧ IsConjInvariantH (scaledFSH ι) ∧
      MonomialsBounded P (scaledFSH ι) (fun _ => 1)

end GroundTheory.Heights₂.Heights.HilbertSamuel
