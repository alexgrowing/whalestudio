import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNefCountLower
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNefCountUpper
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

theorem tendsto_div_of_bounds {h c : ℕ → ℝ} {T : ℝ} (hc : ∀ᶠ n in atTop, 0 < c n)
    (hlo : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, (T - ε) * c n ≤ h n)
    (hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, h n ≤ (T + ε) * c n) :
    Tendsto (fun n => h n / c n) atTop (𝓝 T) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [hc, hlo ((T - a) / 2) (by linarith)] with n hcn hn
    rw [lt_div_iff₀ hcn]
    have := mul_lt_mul_of_pos_right (show a < T - (T - a) / 2 by linarith) hcn
    linarith
  · filter_upwards [hc, hup ((a - T) / 2) (by linarith)] with n hcn hn
    rw [div_lt_iff₀ hcn]
    have := mul_lt_mul_of_pos_right (show T + (a - T) / 2 < a by linarith) hcn
    linarith

theorem eventually_pos_normaliser (D : ℕ) :
    ∀ᶠ n : ℕ in atTop, (0 : ℝ) < (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

theorem MoriwakiHS.of_found (hL : NefCountLower.Statement) (hU : NefCountUpper.Statement) :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement := by
  intro K _ ι _ Ω _ y D A P0 II hII har hb hP0 hs hc hnef hgen hht
  exact tendsto_div_of_bounds (h := smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a))
    (c := fun n : ℕ => (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) (eventually_pos_normaliser D)
    (hL K ι Ω y D A P0 II hII har hb hP0 hs hc hnef hgen hht)
    (hU K ι Ω y D A P0 II hII har hb hP0 hs hc hnef hgen hht)

end

end GroundTheory.Heights₂.Heights.Targets
