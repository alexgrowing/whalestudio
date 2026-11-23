import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

noncomputable section

def LogNormGradDensNonneg.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (s : (Fin (e + 1) → ℂ) → Fin n → ℂ) (y : Fin (e + 1) → ℂ)
    (v : (Fin (e + 1) → ℂ) → ℝ),
    AnalyticAt ℂ s y → s y ≠ 0 →
      0 ≤ gradDens (fun _ : Fin e => (fun x => Real.log (h.dualNorm x)) ∘ s) v v y

end

end GroundTheory.Heights₂.Heights
