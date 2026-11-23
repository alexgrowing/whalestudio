import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

def KHCombCyclic.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (J : ∀ k, Finset (ι k)) (n : ℕ),
    (∀ k, J k = ∅ ∨ J k = Finset.univ) →
      combD S J n (singOne S J n) = 0 ∧
        ∀ f : CombC S J n, combD S J n f = 0 → ∃ s : S, f - s • singOne S J n ∈ combB S J n

end

end GroundTheory.Heights₂.Heights.Kleiman
