import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFStep
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def PFSecAt (I : AllFam) (r : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
    (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin (r + 1) → HermLine ι')
    (s : MRing ι') (a : K' → ℕ),
    IsBlockMap κ v → IsArithVar P' (d + (r + 1)) → IsArithVar (imageZ v P') d → IsFieldIntersection J →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) →
    (∀ k, (N (Fin.last r)).a k = a k) → IsMultiHomog s a → s ∉ P' →
    I K' ι' P' (d + (r + 1)) (Fin.append L' N) =
      (J (fibreIdeal κ G) (r + 1) (fun j => fibreDeg κ (N j).a) : ℝ) * I K ι (imageZ v P') d L

def PFSecRed.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ r : ℕ, PFSecAt I r → PFAt I (r + 1)

section Inhabitants

def fibreLineDeg : Unit ⊕ Unit → ℕ := Sum.elim (fun _ => 0) fun _ => 1

def fibreCoord : MRing PointLineBlocks := X ⟨Sum.inr (), (0 : Fin 2)⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Inter
