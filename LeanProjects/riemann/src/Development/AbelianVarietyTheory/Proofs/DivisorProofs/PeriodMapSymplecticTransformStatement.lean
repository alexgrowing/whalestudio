import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapSymplecticTransform
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_map_symplectic_transform : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ γ : Sp g, IsPeriodMap B (fun b => moeb γ (τ b)) ∧ (∀ b ∈ B, IsUnit (den γ (τ b))) ∧ DifferentiableOn ℂ (reframe τ γ) (cov B g) := by
  first | exact @GlobalTheory.SympBase.main | exact GlobalTheory.SympBase.main | (intros; apply GlobalTheory.SympBase.main <;> assumption)
