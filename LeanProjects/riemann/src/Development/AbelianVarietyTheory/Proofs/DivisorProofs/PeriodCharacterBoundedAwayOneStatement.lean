import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCharacterBoundedAwayOne
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableExpNegL1Norm
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TauPeriod Complex
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_character_bounded_away_one : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ} {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap U τ → ∀ b₀ ∈ U, ∃ r > 0, Metric.closedBall b₀ r ⊆ U ∧ ∃ δ > 0, ∀ n : Fin g → ℤ, n ≠ 0 → ∃ k : Fin g, ∀ b ∈ Metric.closedBall b₀ r, δ ≤ ‖ex n (per (τ b) (Pi.single (Sum.inl k) 1)) - 1‖ := by
  first | exact @GlobalTheory.TauPeriod.exists_ball_norm_ex_row_sub_one_ge | exact GlobalTheory.TauPeriod.exists_ball_norm_ex_row_sub_one_ge | (intros; apply GlobalTheory.TauPeriod.exists_ball_norm_ex_row_sub_one_ge <;> assumption)
