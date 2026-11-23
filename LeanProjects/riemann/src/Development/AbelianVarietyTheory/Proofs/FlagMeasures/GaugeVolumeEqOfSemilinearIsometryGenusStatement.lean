import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeVolumeEqOfSemilinearIsometryGenus
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaugeVolume_eq_of_semilinear_isometry_genus : ∀ (I I' : AutInst) (e : I'.E ≃+* I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), (∀ y, e (star y) = star (e y)) → I'.n = I.n → Aᴴ * I.J * A = I'.J.map e → (∀ y : Fin I'.n → I'.E, y ∈ I'.L ↔ A *ᵥ (fun i => e (y i)) ∈ lamX I (1, xf)) → ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (c' : InfinitePlace I'.F → ℝ) (μf' : Measure I'.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure], IsGaugeAll I c → IsGaugeAll I' c' → gaugeVol I c μf = gaugeVol I' c' μf' := by
  first | exact @GlobalTheory.GaugeTransport.gaugeVol_transport | exact GlobalTheory.GaugeTransport.gaugeVol_transport | (intros; apply GlobalTheory.GaugeTransport.gaugeVol_transport <;> assumption)
