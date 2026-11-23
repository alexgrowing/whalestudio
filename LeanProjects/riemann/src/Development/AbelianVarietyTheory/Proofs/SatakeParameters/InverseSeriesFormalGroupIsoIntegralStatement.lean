import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InverseSeriesFormalGroupIsoIntegral
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverse_series_formalGroup_iso_integral : ∀ (l : ℕ) [Fact l.Prime] (g : Formalism.MainNotions.GL3Theta.G1 l), g.Ok → ∀ (hLT : Formalism.L2.G.Pend.LTIso g) (n : ℕ), ‖PowerSeries.coeff n (Formalism.L2.KerInert.BeCob.vLT hLT)‖ ≤ 1 := by
  first | exact @GlobalTheory.InverseSeriesIntegral.v_integral | exact GlobalTheory.InverseSeriesIntegral.v_integral | (intros; apply GlobalTheory.InverseSeriesIntegral.v_integral <;> assumption)
