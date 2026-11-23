import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerOrthogonalityRelation
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_orthogonality_relation : ∀ (n : ℕ) (f g g' : Sch (Fin n)) (x : EuclideanSpace ℝ (Fin n)),
    ∫ w : Fin n ⊕ Fin n → ℝ, starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * rhoFun w ⇑f x =
      (∫ t, f t * starRingEnd ℂ (g t)) * g' x := by
  first | exact @GlobalTheory.MoyalPointwise.moyal_pointwise | exact GlobalTheory.MoyalPointwise.moyal_pointwise | (intros; apply GlobalTheory.MoyalPointwise.moyal_pointwise <;> assumption)
