import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsExtDelta
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

def ExtNonInt.Statement : Prop :=
  ∀ (D : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (m : ℕ) (ε : ℝ), 1 ≤ D → 0 < ε →
    ∀ u : Fin X.A.n → X.U → ℂ,
      (∀ k, ContinuousOn (u k ∘ (X.A.chart k).symm) (X.A.chart k).target) →
      (∀ k l, ∀ x ∈ (X.A.chart k).source ∩ (X.A.chart l).source,
        u k x = jac X.A k l x * X.L₂.g k l x * X.L.g k l x ^ m * u l x) →
      chartIntegral X.A (fun k y => ENNReal.ofReal (2 ^ D * ‖u k y‖ ^ 2 *
        Real.exp (-X.wt m k y) * extFactor D ε 0 (extEv Z k y))) < ⊤ →
      ∀ x ∈ Z.S, u (chartIdx X.A x) x = 0

end

end GroundTheory.Heights₂.Heights.EffectiveHS
