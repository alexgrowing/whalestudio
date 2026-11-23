import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FlowProgrammeBoundsAndLowLevelOptimum
import Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flow_programme_bounds_and_low_level_optimum : ∀ (l d : ℕ) [NeZero d] (D : ZMod d → ℝ), 2 ≤ l → (∀ a, 0 ≤ D a) →
  rho l * ∑ a, D a ≤ Fnum l d D ∧ (∀ t : ℝ, 0 ≤ t → Fnum l d (fun a => t * D a) = t * Fnum l d D) ∧ Formalism.BasicNotions.lpF l d D = Fnum l d D ∧
  ∀ i₀ : ℕ, ∃ x : ZMod d → ℕ → ℝ, IsFlow l d D x ∧ (∀ a i, i₀ ≤ i → x a i = 0) ∧ gam l * ∑ a, D a - flowVal d x ≤ Fnum l d D + ((l : ℝ) ^ i₀)⁻¹ * ∑ a, D a := by
  first | exact @GlobalTheory.FlowProgrammeFacts.main | exact GlobalTheory.FlowProgrammeFacts.main | (intros; apply GlobalTheory.FlowProgrammeFacts.main <;> assumption)
