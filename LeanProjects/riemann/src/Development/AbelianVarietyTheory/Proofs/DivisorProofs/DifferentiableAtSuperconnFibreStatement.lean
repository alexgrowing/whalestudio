import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtSuperconnFibre
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableAt_superconn_fibre : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ} {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {h : Pt E g → ℝ}, IsPeriodMap B τ → ContDiffOn ℝ ∞ h (cov B g) → (∀ P ∈ cov B g, 0 < h P) → ∀ (β : Fin n → E) (u : ℝ) (f : (Fin g → ℂ) → Ext (n + n + g)), ContDiff ℝ ∞ f → ∀ (b : E), b ∈ B → ∀ (z : Fin g → ℂ), DifferentiableAt ℝ (superconn τ h β u fun P => f P.2) (b, z) := by
  first | exact @GlobalTheory.SuperconnFibreDiff.superconn_fibre_differentiableAt | exact GlobalTheory.SuperconnFibreDiff.superconn_fibre_differentiableAt | (intros; apply GlobalTheory.SuperconnFibreDiff.superconn_fibre_differentiableAt <;> assumption)
