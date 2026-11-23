import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodDatumCurvatureIntegralChange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply
open Matrix MeasureTheory Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_datum_curvature_integral_change : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (γ : Sp g) (j : Fl g → Pt E g → ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (b : E) (u : ℝ) (D : Set (Fl g)) (K : ℝ → (Fin g → ℂ) → (Fin g → ℂ) → Ext (n + n + g) →L[ℂ] Ext (n + n + g)), IsPeriodMap B τ → IsDatum B (fun b => moeb γ (τ b)) (latAct M γ) j h → b ∈ B → IsHeatKernel (fun b => moeb γ (τ b)) (latAct M γ) j h β b u D K → IsHeatKernel τ M (fun l P => j (l ᵥ* (γ⁻¹).mat) (reframe τ γ P)) (fun P => h (reframe τ γ P)) β b u ((fun x : Fl g => x ᵥ* (γ⁻¹).mat) ⁻¹' D) (kerConj n (den γ (τ b)) K) := by
  first | exact @GlobalTheory.TorsionForm.HeatConj.isHeatKernel_kerConj | exact GlobalTheory.TorsionForm.HeatConj.isHeatKernel_kerConj | (intros; apply GlobalTheory.TorsionForm.HeatConj.isHeatKernel_kerConj <;> assumption)
