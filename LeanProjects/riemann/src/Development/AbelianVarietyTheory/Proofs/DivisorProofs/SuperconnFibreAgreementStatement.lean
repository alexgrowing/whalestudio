import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnFibreAgreement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.superconn_fibre_agreement : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ) (s s' : Pt E g → Ext (n + n + g)), IsPeriodMap B τ → ContDiffOn ℝ ∞ h (cov B g) → (∀ P ∈ cov B g, 0 < h P) → ContDiffOn ℝ ∞ s (cov B g) → ContDiffOn ℝ ∞ s' (cov B g) → ∀ b ∈ B, (∀ z, s (b, z) = s' (b, z)) → ∀ z, superconn τ h β u (superconn τ h β u s) (b, z) = superconn τ h β u (superconn τ h β u s') (b, z) := by
  first | exact @GlobalTheory.TorsionForm.Fibrewise.main | exact GlobalTheory.TorsionForm.Fibrewise.main | (intros; apply GlobalTheory.TorsionForm.Fibrewise.main <;> assumption)
