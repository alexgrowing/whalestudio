import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsHorizontalSpanXb
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def ArithmeticIntersectionVertical.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (a : Fin n → K → ℤ) (s : MRing ι) (α : K → ℕ) (W' : Ideal (MRing ι')),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    IsMultiHomog s α → s ∉ imageZ v P' → W' ∈ divSupp P' (rename v s) → ¬ IsHorizontal W' →
    (imageZ v W' ∈ divSupp (imageZ v P') s ∧
        ∀ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' →
          geoNum n W' (fun j => pullDeg κ (a j)) =
            J' (fibreIdeal κ G') 0 Fin.elim0 * geoNum n (imageZ v W') a) ∨
      (imageZ v W' ∉ divSupp (imageZ v P') s ∧ geoNum n W' (fun j => pullDeg κ (a j)) = 0)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
