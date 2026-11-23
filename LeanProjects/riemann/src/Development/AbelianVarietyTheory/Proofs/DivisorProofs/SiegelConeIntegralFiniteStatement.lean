import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelConeIntegralFinite
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
open MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_cone_integral_finite : ∀ (F : Type) [Field F] [NumberField F] (n r : ℕ) {c : ℝ}, 0 < c → ∃ L : ℕ,
    ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal ((1 + ∏ i, t i) ^ L)⁻¹ *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  first | exact @GlobalTheory.SiegelSet.lintegral_cone_decay_lt_top | exact GlobalTheory.SiegelSet.lintegral_cone_decay_lt_top | (intros; apply GlobalTheory.SiegelSet.lintegral_cone_decay_lt_top <;> assumption)
