import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BlockResolutionMetricObjects
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockDefectMetricChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def BlockComplexGramMetricChange.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A' : HermLine ι) (P0' : Ideal (MRing ι))
    (hdeg : A'.a = unitDeg d.k₀) (hc : IsConjInvariantH A') (hle : P0' ≤ mCoordIdeal d.y)
    (hp : IsSemipositiveRel P0' (mCoordIdeal d.y) A'),
    (fun n => blockCChi (d.withMetric A' P0' hdeg hc hle hp) n - blockCChi d n -
        (n : ℝ) ^ (D + 1) / (D.factorial : ℝ) * blockMetricInt d A') =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
