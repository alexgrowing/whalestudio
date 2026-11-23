import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StNbarLeviChartReg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open ReciprocityTheory.AnForm.M (IsCompatChart)

def ProjChartHolo.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D)
    (e : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ)), IsCompatChart M.atlas e →
    ∀ γ : ℂ → (Σ k, ι k) → ℂ, AnalyticAt ℂ γ 0 → (∀ᶠ s in 𝓝 (0 : ℂ), γ s ∈ mcPts (mCoordIdeal D.y)) →
      M.proj (γ 0) ∈ e.source → AnalyticAt ℂ (fun s => e (M.proj (γ s))) 0

end GroundTheory.Heights₂.Heights.NineStatements
