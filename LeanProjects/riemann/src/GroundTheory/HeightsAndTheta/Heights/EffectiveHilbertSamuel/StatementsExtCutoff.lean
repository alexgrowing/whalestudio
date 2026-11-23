import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.ObjectsExtDelta
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal ComplexConjugate

noncomputable section

def ExtCutoff.Statement : Prop :=
  ∀ (D : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (j : ℕ), 1 ≤ D → 2 ≤ j →
    ∀ (g : X.U → ℂ) (θ : ℝ), 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ (F₀ : Fin X.A.n → X.U → ℂ) (G : Fin X.A.n → X.U → ℝ),
        (∀ k, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F₀ k ∘ (X.A.chart k).symm)
          (X.A.chart k).target) ∧
        (∀ k l, ∀ x ∈ (X.A.chart k).source ∩ (X.A.chart l).source,
          F₀ k x = jac X.A k l x * X.L₂.g k l x * X.L.g k l x ^ (D + j) * F₀ l x) ∧
        (∀ k, ∀ x ∉ (X.A.chart k).source, F₀ k x = 0) ∧
        (∀ x ∈ Z.S, res X.A Z.s F₀ x = g x) ∧
        topNormSq X.A (X.wt (D + j)) F₀ ≤ ENNReal.ofReal θ ∧
        (∀ k, ContinuousOn (G k ∘ (X.A.chart k).symm) (X.A.chart k).target) ∧
        (∀ k y, 0 ≤ G k y) ∧
        (∀ k, ∀ y ∈ (X.A.chart k).target, ∀ ξ : Fin D → ℂ,
          ‖dbarPair (F₀ k ∘ (X.A.chart k).symm) y ξ‖ ^ 2 ≤
            9 * extShell ε (extEv Z k ((X.A.chart k).symm y)) * G k ((X.A.chart k).symm y) *
              ‖dbarPair (fun z => (extEv Z k ((X.A.chart k).symm z) : ℂ)) y ξ‖ ^ 2 / ε ^ 4) ∧
        72 * chartIntegral X.A (fun k y => ENNReal.ofReal (2 ^ D * G k y *
            Real.exp (-X.wt (D + j) k y) * (extEv Z k y ^ D)⁻¹ * extShell ε (extEv Z k y))) ≤
          ENNReal.ofReal (36 * Real.log 2 * cD D * rSq Z.c ^ D * sNormSq X.A Z.S (X.wt j) g + θ)

end

end GroundTheory.Heights₂.Heights.EffectiveHS
