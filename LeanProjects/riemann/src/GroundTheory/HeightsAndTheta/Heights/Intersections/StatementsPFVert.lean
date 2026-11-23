import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFStep
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFSecRed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def PFVert.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d r : ℕ)
    (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι')
    (s : MRing ι') (a : K' → ℕ) (W : Ideal (MRing ι')),
    IsBlockMap κ v → IsArithVar P' (d + r + 1) → IsArithVar (imageZ v P') d →
    (∀ j, IsPullHerm κ v (L j) (L' j)) → IsMultiHomog s a → s ∉ P' →
    W ∈ divSupp P' s → ¬ IsHorizontal W →
    geoNum (d + r) W (fun j => (Fin.append L' N j).a) = 0

section Inhabitants

def fibreAtTwo : Ideal (MRing PointLineBlocks) := Ideal.span {C 2}

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Inter
