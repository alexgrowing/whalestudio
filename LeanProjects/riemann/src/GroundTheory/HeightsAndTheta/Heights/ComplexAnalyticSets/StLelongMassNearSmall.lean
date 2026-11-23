import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongRegularise
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def LelongMassNearSmall.Statement : Prop :=
  ∀ (n d : ℕ) (J I : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (f : (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    (∀ i, SmoothNear (zeroSet J) (φ i)) → J ⊔ Ideal.span {linForm u} ≤ I →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) → ContDiff ℝ ∞ f → HasCompactSupport f →
      ∀ δ > 0, ∃ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ ∧
        (∃ U : Set (Fin n → ℂ), IsOpen U ∧ zeroSet I ⊆ U ∧ ∀ x ∈ U, χ x = 1) ∧
        (∀ᶠ ε in 𝓝[>] (0 : ℝ),
          |varInt J (d + 1) (fun x => χ x * f x) (vecCons (logReg u ε) φ)| ≤ δ) ∧
        |∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
            (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
          (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d (fun x => χ x * f x) φ| ≤ δ

end

end GroundTheory.Heights₂.Heights
