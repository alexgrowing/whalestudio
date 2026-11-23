import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StAPrimeChartMargin
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

def APrimeChartLevi.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (k : Fin X.S.R.N),
    ∃ Q : (Fin D.n → ℂ) → (Fin D.n → ℂ) → ℝ,
      ContinuousOn (fun p : (Fin D.n → ℂ) × (Fin D.n → ℂ) => Q p.1 p.2)
        ((X.S.R.chart k).target ×ˢ Set.univ) ∧
      ∀ z ∈ mcPts (mCoordIdeal D.y), X.M.proj z ∈ (X.S.R.chart k).source → ∀ w v,
        IsChartVel X.M (X.S.R.chart k) z w v →
          levi (fun y => Real.log (D.A'.h y)) z w = Q (X.S.R.chart k (X.M.proj z)) v

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
