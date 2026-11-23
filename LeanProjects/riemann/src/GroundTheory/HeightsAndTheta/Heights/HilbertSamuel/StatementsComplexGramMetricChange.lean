import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResolutionMetricObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def ComplexGramMetricChange.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (m₁ : ConeMetric ℂ (Ix κ)) (P0₁ : Ideal (MRing (GlobalTheory κ))) (hs : IsSmoothMetric m₁)
    (hc : IsConjInvariant m₁) (hle : P0₁ ≤ coordIdeal ℤ d.x)
    (hp : IsSemipositiveRel P0₁ (coordIdeal ℤ d.x) (HermLine.ofCone m₁)) (e : Fin (D + 1) → Ix κ),
    IsProjFrame d.x e →
    (fun n => resCChi (d.withMetric m₁ P0₁ hs hc hle hp) n - resCChi d n -
        (n : ℝ) ^ (D + 1) / (D.factorial : ℝ) * resMetricInt d m₁) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
