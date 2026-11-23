import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerRepUnitary
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_rep_unitary : ∀ (n : ℕ) (w : Fin n ⊕ Fin n → ℝ) (u v : EuclideanSpace ℝ (Fin n) → ℂ),
    ∫ x, rhoFun w u x * starRingEnd ℂ (rhoFun w v x) = ∫ x, u x * starRingEnd ℂ (v x) := by
  first | exact @GlobalTheory.RealWeil.integral_rhoFun_mul_conj | exact GlobalTheory.RealWeil.integral_rhoFun_mul_conj | (intros; apply GlobalTheory.RealWeil.integral_rhoFun_mul_conj <;> assumption)
