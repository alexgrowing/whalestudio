import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Dominated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SemiampleNef.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (a : K → ℤ),
    IndefiniteRowSideFullHecke.HilbertSamuel.IsSemiampleOnFibres P a → NefOnFibres P a

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
