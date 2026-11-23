import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OmQuotientTwistDet
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.om_quotient_twist_det : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (μ : kˣ →* ℂˣ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W), OmQuot μ σ τ ↔ OmQuot 1 (twist σ (detChar (Fin r) μ⁻¹)) (twist τ (detChar (Fin n) μ)) := by
  first | exact @GlobalTheory.OmTwist.main | exact GlobalTheory.OmTwist.main | (intros; apply GlobalTheory.OmTwist.main <;> assumption)
