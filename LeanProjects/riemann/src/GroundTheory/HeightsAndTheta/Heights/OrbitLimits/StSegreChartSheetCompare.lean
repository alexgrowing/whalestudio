import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartProjObjects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm oneLine isSmoothHerm_oneLine)
open ComplexSets Matrix

def SegreChartSheetCompare.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin e → HermLine ι), (∀ j, IsSmoothHerm (L j)) →
      ∃ C : ℝ, ∀ J ∈ segreChartComponents P σ i, ∀ (A : Matrix (Fin e) (Fin m) ℂ) (x : Fin m → ℂ)
        (s : (Fin e → ℂ) → Fin m → ℂ), x ∈ zeroSet J → IsSheetAt J A x s →
          |ReciprocityTheory.AnForm.maDens (fun k => chartPot σ i L k ∘ s) (A *ᵥ x)| ≤
            C * |ReciprocityTheory.AnForm.maDens
              (fun _ => (fun w => Real.log ((HermNorm.std m).dualNorm w)) ∘ s) (A *ᵥ x)|

end GroundTheory.Heights₂.Heights
