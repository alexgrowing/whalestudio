import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureReframedMetricEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply
open Matrix MeasureTheory Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvature_reframed_metric_eq : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g) (h : Pt E g → ℝ) (β : Fin n → E) (b : E) (u : ℝ) (f : (Fin g → ℂ) → Ext (n + n + g)), IsPeriodMap B τ → IsPeriodMap B (fun b => moeb γ (τ b)) → ContDiffOn ℝ ∞ h (cov B g) → (∀ P ∈ cov B g, 0 < h P) → b ∈ B → ContDiff ℝ ∞ f → ∀ z, curv τ (fun P => h (reframe τ γ P)) β b u (fun y => frameMap n (den γ (τ b)) (f (y ᵥ* (den γ (τ b))⁻¹))) z = frameMap n (den γ (τ b)) (curv (fun b => moeb γ (τ b)) h β b u f (z ᵥ* (den γ (τ b))⁻¹)) := by
  first | exact @GlobalTheory.TorsionForm.Gauge.curv_conj_closed | exact GlobalTheory.TorsionForm.Gauge.curv_conj_closed | (intros; apply GlobalTheory.TorsionForm.Gauge.curv_conj_closed <;> assumption)
