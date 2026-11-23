import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.CxPts

namespace GlobalTheory.HermIsom

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

def RatIsom [IsIntegral X] (L M : HermLB p) : Prop :=
  ∃ (Δ : CartierDiv X) (r : L.B.ι → X.functionFieldˣ) (s : M.B.ι → X.functionFieldˣ),
    Presents Δ L.B r ∧ Presents Δ M.B s ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) (i : L.B.ι) (j : M.B.ι),
      y ∈ ptsIn p σ (L.B.U i) → y ∈ ptsIn p σ (M.B.U j) →
        (M.φ σ).φ j y = (L.φ σ).φ i y + Real.log (‖ratVal ((s j / r i : X.functionFieldˣ) : X.functionField) y‖ ^ 2)

end GlobalTheory.HermIsom
