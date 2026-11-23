import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffBoundaryParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

noncomputable section

def LogNormEnergyDensNonneg.Statement : Prop :=
  ∀ (n d : ℕ) (h : HermNorm n) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ)
    (v : (Fin (d + 1) → ℂ) → ℝ), AnalyticAt ℂ s y → s y ≠ 0 →
      0 ≤ gradDens (fun _ : Fin d => (fun x => Real.log (h.dualNorm x)) ∘ s) v v y

end

end GroundTheory.Heights₂.Heights
