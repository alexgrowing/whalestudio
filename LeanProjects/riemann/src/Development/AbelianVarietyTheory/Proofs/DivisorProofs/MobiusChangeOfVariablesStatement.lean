import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MobiusChangeOfVariables
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FsOne
open MeasureTheory
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mobius_change_of_variables : ∀ (β c : ℂ), c ≠ 0 → ∀ H : ℂ → ℝ≥0∞, Measurable H →
    ∫⁻ x : ℂ, ENNReal.ofReal (‖c / (1 + β * x) ^ 2‖ ^ 2) * H (c * x / (1 + β * x)) = ∫⁻ y : ℂ, H y := by
  first | exact @GlobalTheory.FibLine.MoebiusLintegral.lintegral_moebius | exact GlobalTheory.FibLine.MoebiusLintegral.lintegral_moebius | (intros; apply GlobalTheory.FibLine.MoebiusLintegral.lintegral_moebius <;> assumption)
