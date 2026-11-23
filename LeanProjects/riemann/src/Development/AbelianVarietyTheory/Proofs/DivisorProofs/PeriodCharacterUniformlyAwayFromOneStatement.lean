import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCharacterUniformlyAwayFromOne
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChSingle
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.FamilyFourier
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_character_uniformly_away_from_one : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap U τ → ∀ b₀ ∈ U, ∃ V : Set E, IsOpen V ∧ b₀ ∈ V ∧ V ⊆ U ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ n : Fin g → ℤ, n ≠ 0 → ∃ k : Fin g, ∀ b ∈ V, δ ≤ ‖ch n (per (τ b) (Pi.single (Sum.inl k) (1 : ℝ))) - 1‖ := by
  first | exact @GlobalTheory.RowChoice.rowChoice | exact GlobalTheory.RowChoice.rowChoice | (intros; apply GlobalTheory.RowChoice.rowChoice <;> assumption)
