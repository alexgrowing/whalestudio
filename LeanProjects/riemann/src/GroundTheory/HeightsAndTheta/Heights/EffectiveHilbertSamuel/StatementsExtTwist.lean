import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.ObjectsExtDelta
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal ComplexConjugate

noncomputable section

def ExtTwist.Statement : Prop :=
  ∀ (D : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (j : ℕ), 1 ≤ D → 2 ≤ j →
    ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      (∀ k, X.A.SmoothOn (X.A.chart k).source (fun y => extPsi Z j δ k y + extPhi Z ε k y)) ∧
      (∀ k, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (extPhi Z ε k ∘ (X.A.chart k).symm)
        (X.A.chart k).target) ∧
      (∀ k l, ∀ x ∈ (X.A.chart k).source ∩ (X.A.chart l).source,
        extPsi Z j δ k x = extPsi Z j δ l x + Real.log (‖X.L₂.g k l x * X.L.g k l x ^ (D + j)‖ ^ 2) ∧
          extPhi Z ε k x = extPhi Z ε l x) ∧
      (∀ k, ∀ y ∈ (X.A.chart k).target, ∀ ξ : Fin D → ℂ,
        extTheta ε (extEv Z k ((X.A.chart k).symm y)) * extOmega Z ε k y ξ ≤
          levi ((fun x => extPsi Z j δ k x + extPhi Z ε k x) ∘ (X.A.chart k).symm) y ξ) ∧
      (∀ k, ∀ y ∈ (X.A.chart k).target, ∀ ξ : Fin D → ℂ,
        ‖dbarPair (fun z => (extPhi Z ε k ((X.A.chart k).symm z) : ℂ)) y ξ‖ ^ 2 =
          (curvK (extX ε (extEv Z k ((X.A.chart k).symm y))) /
            curvEta (extX ε (extEv Z k ((X.A.chart k).symm y)))) ^ 2 * extOmega Z ε k y ξ)

end

end GroundTheory.Heights₂.Heights.EffectiveHS
