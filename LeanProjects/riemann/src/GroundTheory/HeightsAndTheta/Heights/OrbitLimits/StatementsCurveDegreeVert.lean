import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import GroundTheory.HeightsAndTheta.Heights.Intersections.SameOrbitOneSpecZ
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveCountObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter

def CurveDegreeVert.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem) (c : ∀ k, ι k)
    (R : Finset ((Σ k, ι k) → ℂ)) (b d : K → ℕ),
    IsIntersectionSystem II → IsArithVar P 1 → IsSmoothHerm A → (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) →
    (∀ t ∈ R, t ∈ mcPts P) → (∀ z ∈ mcPts P, ∃! t, t ∈ R ∧ SameOrbit z t) →
    (∀ k, (d k : ℤ) = A.a k + b k) →
    II K ι P 1 (fun _ => A) =
      vertR P (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c d) -
        vertR P (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c b) +
        ∑ t ∈ R, Real.log (chartRadius A c t)

namespace CurveDegreeVert

end CurveDegreeVert

end GroundTheory.Heights₂.Heights.Targets
