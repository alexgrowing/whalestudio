import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StAPrimeMarginCharts
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GroundTheory.Heights₂.Heights.LowerBoundFree

def ChartVelLiftCharts.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D)
    (C : GroundTheory.Heights₂.Heights.Regular.PotentialCharts M.atlas) (k : Fin C.N),
    ∀ y ∈ (C.chart k).target, ∀ v : Fin D.n → ℂ, v ≠ 0 →
      ∃ z ∈ mcPts (mCoordIdeal D.y), M.proj z = (C.chart k).symm y ∧ ∃ w,
        IsChartVel M (C.chart k) z w v ∧ IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) z w ∧
          ∀ c : K → ℂ, w ≠ torusSmul c z

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.NineStatements
