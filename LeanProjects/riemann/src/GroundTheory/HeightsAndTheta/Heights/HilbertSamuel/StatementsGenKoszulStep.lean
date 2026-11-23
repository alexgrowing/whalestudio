import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAmpleOfGenTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenKoszulStep.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (α : K → ℤ),
    IsMultiHomogIdeal V → KH.GeneratedV S V α →
    ∃ R : ℕ, ∀ c : K → ℤ,
      (∀ p : ℕ, 1 ≤ p → p ≤ R → ∀ i : ℕ, 1 ≤ i →
        Subsingleton (KH.cechHc ι (KH.quotPart S V) (c - (p : ℤ) • α) i)) →
      ∀ i : ℕ, 1 ≤ i → Subsingleton (KH.cechHc ι (KH.quotPart S V) c i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
