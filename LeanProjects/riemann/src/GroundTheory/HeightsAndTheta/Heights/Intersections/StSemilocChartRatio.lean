import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocRankFrac
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def SemilocChartRatio.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (i' : ∀ k', ι' k'), IsBlockMap κ v → IsArithVar P' (n + 1) →
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    (∀ k', (X ⟨k', i' k'⟩ : MRing ι') ∉ P') →
    ∀ q : Σ k', ι' k', ∃ b b' : semiLocRing P' (fibreOver v P' W),
      (b' : FractionRing (MRing ι' ⧸ P')) ≠ 0 ∧
      (b : FractionRing (MRing ι' ⧸ P')) * algebraMap _ _ (Ideal.Quotient.mk P' (X ⟨q.1, i' q.1⟩)) =
        (b' : FractionRing (MRing ι' ⧸ P')) * algebraMap _ _ (Ideal.Quotient.mk P' (X q))

end GroundTheory.Heights₂.Heights.Inter
