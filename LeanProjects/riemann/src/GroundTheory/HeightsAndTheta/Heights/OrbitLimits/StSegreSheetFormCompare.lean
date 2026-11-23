import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartProjObjects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm pot segre oneLine isSmoothHerm_oneLine)

def SegreSheetFormCompare.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (e : ℕ) (L : Fin e → HermLine ι),
    (∀ j, IsSmoothHerm (L j)) →
      ∃ C : ℝ, ∀ (z : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (U : Set (Fin e → ℂ)) (y : Fin e → ℂ),
        IsOpen U → y ∈ U → DifferentiableOn ℂ z U → (∀ k, ∃ j, z y ⟨k, j⟩ ≠ 0) →
          |ReciprocityTheory.AnForm.maDens (fun j => pot L j ∘ z) y| ≤
            C * ReciprocityTheory.AnForm.maDens
              (fun _ => (fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z) y

end GroundTheory.Heights₂.Heights
