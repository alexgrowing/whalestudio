import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuSheetLeviNonneg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.Regular (RegChartData)

def SheetChartHolo.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (M : CxModel P n) (R : RegChartData M.atlas) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    ∀ᵐ y : Fin n → ℂ, ∀ (w : ((k : K) → ι k) → ℂ) (γ : (Fin n → ℂ) → (Σ k, ι k) → ℂ),
      IsSheet P Q y w γ → ∃ j : Fin R.N, M.proj (γ y) ∈ (R.chart j).source ∧ M.proj (γ y) ∈ R.Yo ∧
        ∀ᶠ y' in 𝓝 y, M.proj (γ y') ∈ (R.chart j).source ∧
          DifferentiableAt ℂ (fun y'' => R.chart j (M.proj (γ y''))) y'

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
