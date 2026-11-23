import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntegralIntegrable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_integrable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (r t : ℕ) (μ : kˣ →* ℂˣ),
    r ≤ t → IsSmoothChar μ → IsUnitaryChar μ → ∀ (h : GL (Fin (r + t)) k)
      (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ), Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
      Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) (volGL ν (Fin r)) := by
  first | exact @GlobalTheory.GodementJacquet.integrable_om_eMat | exact GlobalTheory.GodementJacquet.integrable_om_eMat | (intros; apply GlobalTheory.GodementJacquet.integrable_om_eMat <;> assumption)
