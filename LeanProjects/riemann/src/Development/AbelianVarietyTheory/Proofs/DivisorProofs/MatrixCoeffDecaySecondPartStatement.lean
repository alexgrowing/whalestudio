import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixCoeffDecaySecondPart
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coeff_decay_second_part : ∀ (n : ℕ) (g g' : Sch (Fin n)) (N : ℕ), ∃ C : ℝ, ∀ w : Fin n ⊕ Fin n → ℝ, ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖qPart w‖) ^ N ≤ C := by
  first | exact @GlobalTheory.RealWeil.coef_qDecay | exact GlobalTheory.RealWeil.coef_qDecay | (intros; apply GlobalTheory.RealWeil.coef_qDecay <;> assumption)
