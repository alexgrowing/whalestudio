import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoBallMeanBigCellWeight
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_ball_mean_bigCellWeight : ∀ (k r : ℕ), Tendsto (fun ρ : ℝ => (∫⁻ x in Metric.ball (fun _ => 1 : Fin r → ℂ) ρ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r x)) / volume (Metric.ball (0 : Fin r → ℂ) ρ)) (𝓝[>] 0) (𝓝 1) := by
  first | exact @GlobalTheory.CellDens.tendsto_mean_cWeight | exact GlobalTheory.CellDens.tendsto_mean_cWeight | (intros; apply GlobalTheory.CellDens.tendsto_mean_cWeight <;> assumption)
