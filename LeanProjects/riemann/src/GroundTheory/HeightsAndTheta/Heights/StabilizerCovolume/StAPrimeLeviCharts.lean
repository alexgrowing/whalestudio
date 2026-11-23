import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StAPrimeMarginCharts
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm (levi)

def APrimeLeviCharts.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D)
    (C : GroundTheory.Heights₂.Heights.Regular.PotentialCharts M.atlas) (k : Fin C.N),
    ∃ Q : (Fin D.n → ℂ) → (Fin D.n → ℂ) → ℝ,
      ContinuousOn (fun p : (Fin D.n → ℂ) × (Fin D.n → ℂ) => Q p.1 p.2)
        ((C.chart k).target ×ˢ Set.univ) ∧
      ∀ z ∈ mcPts (mCoordIdeal D.y), M.proj z ∈ (C.chart k).source → ∀ w v,
        IsChartVel M (C.chart k) z w v →
          levi (fun y => Real.log (D.A'.h y)) z w = Q (C.chart k (M.proj z)) v

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.NineStatements
