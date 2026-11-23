import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsPrimeSpanXb
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def ArithmeticIntersectionHorizontal.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ n : ℕ, GenDegAt I n →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι'))
      (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (s : MRing ι) (α : K → ℕ) (W' : Ideal (MRing ι')),
      IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
      (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
      IsMultiHomog s α → s ∉ imageZ v P' → W' ∈ divSupp P' (rename v s) → IsHorizontal W' →
      (imageZ v W' ∈ divSupp (imageZ v P') s ∧
          ∀ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' →
            I K' ι' W' n L' = (J' (fibreIdeal κ G') 0 Fin.elim0 : ℝ) * I K ι (imageZ v W') n L) ∨
        (imageZ v W' ∉ divSupp (imageZ v P') s ∧ I K' ι' W' n L' = 0)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
