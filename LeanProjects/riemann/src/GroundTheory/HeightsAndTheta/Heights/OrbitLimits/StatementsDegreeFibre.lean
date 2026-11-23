import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def FibreDegreeSum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e : ℕ) (a : Fin e → K → ℤ) (p : ℕ),
    IsArithVar P (e + 1) → p.Prime →
      NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) a =
        ∑ᶠ V ∈ divSupp P (C (p : ℤ)), (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℤ) * geoNum e V a

end GroundTheory.Heights₂.Heights.Targets
