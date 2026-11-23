import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuSheetLeviNonneg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def RefAlongSheet.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (A : HermLine ι) (S : LogLogRegularisationSetting M Xo A)
    (γ : (Fin n → ℂ) → (Σ k, ι k) → ℂ) (y : Fin n → ℂ) (j : Fin S.R.N),
    (∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ γ y' ∈ mcPts P) →
    M.proj (γ y) ∈ (S.R.chart j).source →
    (∀ᶠ y' in 𝓝 y, M.proj (γ y') ∈ (S.R.chart j).source ∧
      DifferentiableAt ℂ (fun y'' => S.R.chart j (M.proj (γ y''))) y') →
    ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G y ∧ ∀ᶠ y' in 𝓝 y,
      Real.log (S.ref.h (γ y')) = S.R.q j (S.R.chart j (M.proj (γ y'))) + (G y').re

end GroundTheory.Heights₂.Heights.LowerBoundFree
