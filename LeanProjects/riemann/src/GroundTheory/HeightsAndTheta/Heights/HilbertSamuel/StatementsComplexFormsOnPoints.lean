import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ComplexFormsOnPoints.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    P.IsPrime → IsRelevant P →
    ∀ F : MvPolynomial (Σ k, ι k) ℂ, (∀ z ∈ mcPts P, eval z F = 0) →
      F ∈ P.map (MvPolynomial.map (Int.castRingHom ℂ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
