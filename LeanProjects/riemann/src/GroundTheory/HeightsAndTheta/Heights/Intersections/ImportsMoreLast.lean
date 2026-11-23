import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreTail
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def ArithmeticIntersectionFibreMultiHomogeneous.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (p : ℕ) [Fact p.Prime] (W' : Ideal (MRing ι')),
    IsBlockMap κ v → ((p : ℕ) : MRing ι') ∈ W' →
    IsMultiHomogIdeal (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) →
    ∀ G' : GenFibre v W', IsMultiHomogIdeal (fibreIdeal κ G')

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
