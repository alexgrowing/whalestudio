import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.PullBad
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def FibreIsolFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ),
    IsBlockMap κ v → IsArithVar P' (n + 1) →
    ∀ u : (Σ k, ι k) → ℂ, ∃ T : Finset ((Σ k', ι' k') → ℂ),
      ∀ z' ∈ mcPts P', SameOrbit (fun p => z' (v p)) u →
        (∃ ε > 0, ∀ z'' ∈ mcPts P', SameOrbit (fun p => z'' (v p)) u → dist z'' z' < ε →
          SameOrbit z'' z') →
        ∃ t ∈ T, SameOrbit z' t

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
