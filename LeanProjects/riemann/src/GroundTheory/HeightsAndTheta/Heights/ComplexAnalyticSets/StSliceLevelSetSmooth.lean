import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutDecay
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

def SliceLevelSetSmooth.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (ℓ : Fin n → ℂ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)
    (ψ : ℝ → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) g → linForm ℓ ∉ W →
    IsFiniteProjection (W ⊔ Ideal.span {linForm ℓ - 1}) A → ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    (∀ r, 0 ≤ ψ r) →
      Integrable (fun y => sheetSum (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x s =>
          |ψ (Real.log (h.dualNorm x)) *
            gradDens (fun _ : Fin e => (fun x => Real.log (h.dualNorm x)) ∘ s)
              ((fun x => Real.log (h.dualNorm x)) ∘ s) ((fun x => Real.log (h.dualNorm x)) ∘ s) y|) y) ∧
        (∫ y, sheetSum (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x s =>
          |ψ (Real.log (h.dualNorm x)) *
            gradDens (fun _ : Fin e => (fun x => Real.log (h.dualNorm x)) ∘ s)
              ((fun x => Real.log (h.dualNorm x)) ∘ s) ((fun x => Real.log (h.dualNorm x)) ∘ s) y|) y) ≤
          (∫ y, chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
              (fun _ x => Real.log (h.dualNorm x)) y) * ∫ r, |ψ r|

def SliceLevelSetSmooth.bump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

end

end GroundTheory.Heights₂.Heights
