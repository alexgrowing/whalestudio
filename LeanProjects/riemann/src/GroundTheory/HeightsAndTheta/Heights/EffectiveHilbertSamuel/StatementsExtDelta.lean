import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Statements
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.PCurvature
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

def extEv {D : ℕ} {X : EmbDatum D} (Z : ZeroDatum X) (k : Fin X.A.n) (y : X.U) : ℝ :=
  (∑ i, ‖Z.s i k y‖ ^ 2) * Real.exp (-fsWeight X.e k y) / rSq Z.c

def extX (ε t : ℝ) : ℝ := 1 + Real.log (1 + ε ^ 2) - Real.log (t + ε ^ 2)

def extDen (ε t : ℝ) : ℝ := (extX ε t + 1) ^ 2 + curvEta (extX ε t)

def extFactor (D : ℕ) (ε δ t : ℝ) : ℝ := ((t + δ ^ 2) ^ D)⁻¹ / extDen ε t

def ExtDelta.Statement : Prop :=
  ∀ (D : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (j : ℕ), 1 ≤ D → 2 ≤ j →
    ∀ (g : X.U → ℂ) (θ : ℝ), 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ F₀ : Fin X.A.n → X.U → ℂ,
        (∀ k, ContinuousOn (F₀ k ∘ (X.A.chart k).symm) (X.A.chart k).target) ∧
        (∀ k l, ∀ x ∈ (X.A.chart k).source ∩ (X.A.chart l).source,
          F₀ k x = jac X.A k l x * X.L₂.g k l x * X.L.g k l x ^ (D + j) * F₀ l x) ∧
        (∀ k, ∀ x ∉ (X.A.chart k).source, F₀ k x = 0) ∧
        (∀ x ∈ Z.S, res X.A Z.s F₀ x = g x) ∧
        topNormSq X.A (X.wt (D + j)) F₀ ≤ ENNReal.ofReal θ ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ ε → ∃ F ∈ topSections X.A X.L₂ X.L (D + j),
          chartIntegral X.A (fun k y => ENNReal.ofReal (2 ^ D * ‖F₀ k y - F k y‖ ^ 2 *
            Real.exp (-X.wt (D + j) k y) * extFactor D ε δ (extEv Z k y))) ≤
          ENNReal.ofReal (36 * Real.log 2 * cD D * rSq Z.c ^ D * sNormSq X.A Z.S (X.wt j) g + θ)

end

end GroundTheory.Heights₂.Heights.EffectiveHS
