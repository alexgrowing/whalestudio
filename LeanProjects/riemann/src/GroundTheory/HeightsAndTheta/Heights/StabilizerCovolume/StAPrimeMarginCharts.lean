import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StMUcChartSemipos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StNbarLeviChart
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm (levi)

def APrimeMarginCharts.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D)
    (C : GroundTheory.Heights₂.Heights.Regular.PotentialCharts M.atlas),
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ u, ∀ k : Fin C.N, M.proj z ∈ C.mid k →
      ∀ v : Fin D.n → ℂ, IsChartVel M (C.chart k) z u v →
        c * ‖v‖ ^ 2 ≤ levi (fun y => Real.log (D.A'.h y)) z u

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.NineStatements
