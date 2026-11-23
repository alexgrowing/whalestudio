import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReframeVerticalDerivative
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reframe_vertical_derivative : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g), IsPeriodMap B τ → IsPeriodMap B (fun b => moeb γ (τ b)) → ∀ P ∈ cov B g, DifferentiableAt ℂ (reframe τ γ) P ∧ ∀ a : Fin g, fderiv ℝ (reframe τ γ) P (vert E a) = ∑ c, (den γ (τ P.1))⁻¹ a c • vert E c := by
  first | exact @GlobalTheory.ReframeVert.reframe_vert | exact GlobalTheory.ReframeVert.reframe_vert | (intros; apply GlobalTheory.ReframeVert.reframe_vert <;> assumption)
