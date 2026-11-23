import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.ObjectsExtDelta
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal ComplexConjugate

noncomputable section

def ExtShell.Statement : Prop :=
  ∀ (D : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (m : ℕ), 1 ≤ D →
    ∀ (g : X.U → ℂ) (W : Set X.U) (gt : Fin X.A.n → X.U → ℂ), IsOpen W → Z.S ⊆ W →
      (∀ k, ContinuousOn (gt k ∘ (X.A.chart k).symm)
        ((X.A.chart k).target ∩ (X.A.chart k).symm ⁻¹' W)) →
      (∀ k l, ∀ x ∈ (X.A.chart k).source ∩ (X.A.chart l).source ∩ W,
        gt k x = jac X.A k l x * X.L₂.g k l x * X.L.g k l x ^ (D + m) * gt l x) →
      (∀ x ∈ Z.S, gt (chartIdx X.A x) x = g x * sJac X.A Z.s (chartIdx X.A x) x) →
      Tendsto (fun ε : ℝ => chartIntegral X.A (fun k y => ENNReal.ofReal (2 ^ D * ‖gt k y‖ ^ 2 *
          Real.exp (-X.wt (D + m) k y) * (extEv Z k y ^ D)⁻¹ * extShell ε (extEv Z k y))))
        (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal (Real.log 2 / 2 * cD D * rSq Z.c ^ D * sNormSq X.A Z.S (X.wt m) g)))

end

end GroundTheory.Heights₂.Heights.EffectiveHS
