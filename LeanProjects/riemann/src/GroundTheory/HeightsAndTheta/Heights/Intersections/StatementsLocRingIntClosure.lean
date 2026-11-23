import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocRing
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def LocRingIntClosureFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (_hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)),
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    haveI := hP'.2.1.1
    letI := ((fracMapZ v P').comp (locRing (imageZ v P') W).subtype).toAlgebra
    letI : Module (locRing (imageZ v P') W) (FractionRing (MRing ι' ⧸ P')) := Algebra.toModule
    ∃ t : Finset (FractionRing (MRing ι' ⧸ P')), ∀ x ∈ semiLocRing P' ∅,
      IsIntegral (locRing (imageZ v P') W) x → x ∈ Submodule.span (locRing (imageZ v P') W) (t : Set _)

end GroundTheory.Heights₂.Heights.Inter
