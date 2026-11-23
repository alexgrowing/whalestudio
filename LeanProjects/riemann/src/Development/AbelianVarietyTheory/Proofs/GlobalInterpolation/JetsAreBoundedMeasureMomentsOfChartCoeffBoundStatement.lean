import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetsAreBoundedMeasureMomentsOfChartCoeffBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetsAreBoundedMeasureMoments_of_chart_coeff_bound : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ), Differentiable ℂ G → Bd 1 (hat ι (C ω * logS) G) → MomInt ι (fun _ : Unit => ι.symm ω) G := by
  first | exact @GlobalTheory.MomOneAmice.momInt_of_bd_hat | exact GlobalTheory.MomOneAmice.momInt_of_bd_hat | (intros; apply GlobalTheory.MomOneAmice.momInt_of_bd_hat <;> assumption)
