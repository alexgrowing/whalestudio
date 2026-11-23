import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocLength
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def SemilocLengthSum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s t : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (E : Ideal (MRing ι') → ℤ) (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1))
    (y : locRing (imageZ v P') W),
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → IsMultiHomog t α → s ∉ imageZ v P' →
    W ∈ divSupp (imageZ v P') s → t ∉ W →
    (y : FractionRing (MRing ι ⧸ imageZ v P')) * algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') t) =
      algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') s) →
    (∀ W' ∈ fibreOver v P' W, rename v s ∈ W' →
      ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)),
        IsFieldIntersection J' ∧ E W' = J' (fibreIdeal κ G') 0 Fin.elim0) →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    (fibreOver v P' W).Finite ∧
      ∃ N : ℕ, Module.length (locRing (imageZ v P') W)
          (semiLocRing P' (fibreOver v P' W) ⧸ LinearMap.range
            (LinearMap.lsmul (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) y)) = N ∧
        (N : ℤ) = ∑ᶠ W' ∈ {W' | W' ∈ fibreOver v P' W ∧ rename v s ∈ W'},
          ((Module.length (locRing P' W') (locRing P' W' ⧸ locIdeal P' W' (fracMapZ v P' y))).toNat : ℤ) * E W'

end GroundTheory.Heights₂.Heights.Inter
