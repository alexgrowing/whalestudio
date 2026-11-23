import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StProjChartHolo
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology

def RefChartDisc.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) (M : XModel D)
    (S : LogLogRegularisationSetting M D.Xo (muLine H)) (k : Fin S.R.N) (γ : ℂ → (Σ k, ι k) → ℂ), AnalyticAt ℂ γ 0 →
    (∀ᶠ s in 𝓝 (0 : ℂ), γ s ∈ mcPts (mCoordIdeal D.y)) → M.proj (γ 0) ∈ (S.R.chart k).source →
      ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ ∀ᶠ s in 𝓝 (0 : ℂ),
        Real.log (S.ref.h (γ s)) = S.R.q k (S.R.chart k (M.proj (γ s))) - (G s).re

end GroundTheory.Heights₂.Heights.NineStatements
