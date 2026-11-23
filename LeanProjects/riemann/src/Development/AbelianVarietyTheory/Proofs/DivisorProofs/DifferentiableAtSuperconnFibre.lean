import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnectionContDiffOn
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff

set_option autoImplicit false

namespace GlobalTheory.SuperconnFibreDiff

theorem superconn_fibre_differentiableAt : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ} {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {h : Pt E g → ℝ}, IsPeriodMap B τ → ContDiffOn ℝ ∞ h (cov B g) → (∀ P ∈ cov B g, 0 < h P) → ∀ (β : Fin n → E) (u : ℝ) (f : (Fin g → ℂ) → Ext (n + n + g)), ContDiff ℝ ∞ f → ∀ (b : E), b ∈ B → ∀ (z : Fin g → ℂ), DifferentiableAt ℝ (superconn τ h β u fun P => f P.2) (b, z) := by
  intro E _ _ _ g n B τ h hτ hh hpos β u f hf b hb z
  have hU := GlobalTheory.TorsionForm.SuperconnSmooth.isOpen_cov (g := g) hτ
  have hs : ContDiffOn ℝ ∞ (fun P : Pt E g => f P.2) (cov B g) :=
    (hf.comp contDiff_snd).contDiffOn
  have hc := GlobalTheory.TorsionForm.SuperconnSmooth.superconn_contDiffOn E g n B τ h β u _ hτ hh hpos hs
  have hmem : ((b, z) : Pt E g) ∈ cov B g := by
    simp [cov, hb]
  exact (hc.contDiffAt (hU.mem_nhds hmem)).differentiableAt (by simp)

end GlobalTheory.SuperconnFibreDiff
