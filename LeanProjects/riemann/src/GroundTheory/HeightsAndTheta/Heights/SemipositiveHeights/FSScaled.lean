import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConstantShift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

variable {K : Type} [Fintype K]

def fsScaled (ι : K → Type) [∀ k, Fintype (ι k)] (C : ℝ) : HermLine ι :=
  HermLine.constShift (fsH ι) (-Real.log C)

theorem fsScaled_a (ι : K → Type) [∀ k, Fintype (ι k)] (C : ℝ) : (fsScaled ι C).a = fun _ => 1 := by
  funext k
  simp [fsScaled, HermLine.constShift, HermLine.tensor, fsH, HermLine.ofMetrics, HermLine.ofWeight]

theorem fsScaled_h (ι : K → Type) [∀ k, Fintype (ι k)] {C : ℝ} (hC : 0 < C) (z : (Σ k, ι k) → ℂ) :
    (fsScaled ι C).h z = C * (fsH ι).h z := by
  simp [fsScaled, HermLine.constShift, HermLine.tensor, HermLine.ofWeight, Real.exp_log hC, mul_comm]

end

end GroundTheory.Heights₂.Heights.ForSecondHalf
