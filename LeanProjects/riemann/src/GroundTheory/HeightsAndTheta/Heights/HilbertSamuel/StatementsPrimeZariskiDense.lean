import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def PrimeZariskiDense.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (j : MRing ι),
    P.IsPrime → j ∉ P →
    ∀ g : MvPolynomial (Σ k, ι k) ℂ,
      (∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) j) ≠ 0 → eval z g = 0) →
      ∀ z ∈ mcPts P, eval z g = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
