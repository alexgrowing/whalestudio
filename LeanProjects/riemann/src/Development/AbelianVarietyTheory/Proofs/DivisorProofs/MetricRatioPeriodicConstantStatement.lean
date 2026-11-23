import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricRatioPeriodicConstant
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusFundamentalDomainCovers
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_ratio_periodic_constant : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.IsPeriodMap B τ → ∀ (j : Fl g → Pt E g → ℂ) (m h : Pt E g → ℝ) (φ : Pt E g → ℂ), (∀ P ∈ cov B g, 0 < m P) → (∀ P ∈ cov B g, 0 < h P) → (∀ l ∈ stdLat g, ∀ P ∈ cov B g, m (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.transl τ l P) * ‖j l P‖ ^ 2 = m P) → (∀ l ∈ stdLat g, ∀ P ∈ cov B g, h (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.transl τ l P) * ‖j l P‖ ^ 2 = h P) → (∀ b ∈ B, Continuous fun z => m (b, z)) → (∀ b ∈ B, Continuous fun z => h (b, z)) → (∀ P ∈ cov B g, m (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.mulN 2 P) = m P ^ 4 * ‖φ P‖ ^ 2) → (∀ P ∈ cov B g, h (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.mulN 2 P) = h P ^ 4 * ‖φ P‖ ^ 2) → Set.EqOn m h (cov B g) := by
  first | exact @GlobalTheory.TateUniq.metric_eq_of_doubling | exact GlobalTheory.TateUniq.metric_eq_of_doubling | (intros; apply GlobalTheory.TateUniq.metric_eq_of_doubling <;> assumption)
