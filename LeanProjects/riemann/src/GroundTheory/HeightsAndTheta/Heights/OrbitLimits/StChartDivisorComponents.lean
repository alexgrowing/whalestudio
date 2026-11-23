import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartSection
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsSectionOn divSupp IsHorizontal PBlk fsLine Xc)
open GroundTheory.Heights₂.Heights (segreChartComponents)

def ChartDivisorComponents.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (A : HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → IsSectionOn P A s →
      (∀ J ∈ segreChartComponents P σ i, ∀ W' : Ideal (MvPolynomial (Fin m) ℂ),
        W' ∈ (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes ↔
          J ≤ W' ∧ ∃ W, (W ∈ divSupp P s ∧ IsHorizontal W) ∧ W' ∈ segreChartComponents W σ i) ∧
      ∀ W₁ W₂, W₁ ∈ divSupp P s ∧ IsHorizontal W₁ → W₂ ∈ divSupp P s ∧ IsHorizontal W₂ →
        ∀ W' ∈ segreChartComponents W₁ σ i, W' ∈ segreChartComponents W₂ σ i → W₁ = W₂

end GroundTheory.Heights₂.Heights.Targets
