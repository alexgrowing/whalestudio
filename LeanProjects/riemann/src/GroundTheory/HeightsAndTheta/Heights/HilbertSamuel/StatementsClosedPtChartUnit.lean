import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenNear
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ClosedPtChartUnit.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRingOver S ι)), IsClosedMultiPt P →
    ∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, ∀ i ∈ I k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P) →
    ∀ (f : MRingOver S ι) (a : K → ℕ), IsMultiHomog f a → f ∉ P →
      ∃ t ∈ KH.cellMon S I, ∃ (g : MRingOver S ι) (b : K → ℕ),
        IsMultiHomog t (a + b) ∧ IsMultiHomog g b ∧ t - g * f ∈ P

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
