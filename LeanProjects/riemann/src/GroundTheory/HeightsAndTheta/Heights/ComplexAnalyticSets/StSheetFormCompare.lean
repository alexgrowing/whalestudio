import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutOffLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SheetFormCompare.Statement : Prop :=
  ∀ (n D : ℕ) (h : HermNorm n) (c : Fin D → ℝ) (ψ : Fin D → (Fin n → ℂ) → ℝ),
    (∀ (k : Fin D) (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → ψ k (t • x) = ψ k x) →
    (∀ k, ContDiffOn ℝ ∞ (ψ k) {x | x ≠ 0}) →
      ∃ C : ℝ, ∀ (s : (Fin D → ℂ) → Fin n → ℂ) (U : Set (Fin D → ℂ)) (y : Fin D → ℂ),
        IsOpen U → y ∈ U → DifferentiableOn ℂ s U → s y ≠ 0 →
          |ReciprocityTheory.AnForm.maDens (fun k => (fun x => c k * Real.log (h.dualNorm x) + ψ k x) ∘ s) y| ≤
            C * ReciprocityTheory.AnForm.maDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y

end

end GroundTheory.Heights₂.Heights
