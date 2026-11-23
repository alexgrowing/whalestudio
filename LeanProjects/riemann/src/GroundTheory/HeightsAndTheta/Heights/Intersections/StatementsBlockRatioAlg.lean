import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsBlockGenFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def BlockRatioAlg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    ∀ q c : Σ k', ι' k', q.1 = c.1 → (X c : MRing ι') ∉ P' →
      ∃ (m : ℕ) (A : Fin (m + 1) → MRing ι) (a : K → ℕ), (∀ j, IsMultiHomog (A j) a) ∧
        A (Fin.last m) ∉ imageZ v P' ∧
        ∑ j : Fin (m + 1), rename v (A j) * X q ^ (j : ℕ) * X c ^ (m - j : ℕ) ∈ P'

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
