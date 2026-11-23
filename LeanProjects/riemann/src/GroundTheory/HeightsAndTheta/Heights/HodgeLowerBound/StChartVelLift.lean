import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StAPrimeChartMargin
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def ChartVelLift.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (k : Fin X.S.R.N),
    ∀ y ∈ (X.S.R.chart k).target, ∀ v : Fin D.n → ℂ, v ≠ 0 →
      ∃ z ∈ mcPts (mCoordIdeal D.y), X.M.proj z = (X.S.R.chart k).symm y ∧ ∃ w,
        IsChartVel X.M (X.S.R.chart k) z w v ∧ IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) z w ∧
          ∀ c : K → ℂ, w ≠ torusSmul c z

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
