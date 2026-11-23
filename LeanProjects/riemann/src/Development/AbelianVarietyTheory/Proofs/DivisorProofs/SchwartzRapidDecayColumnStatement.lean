import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzRapidDecayColumn
import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL
open Classical MeasureTheory NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_rapid_decay_column : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (r : ℕ) (f : SchwartzMap (Fin a → GlobalTheory.CuspRep.Cinf E) ℂ), GlobalTheory.JSW.IsRapidInf (volume : Measure (Fin a → GlobalTheory.CuspRep.Cinf E)) (fun x => f x) (GlobalTheory.JSW.colU r) := by
  first | exact @GlobalTheory.JSW.isRapidInf_colU | exact GlobalTheory.JSW.isRapidInf_colU | (intros; apply GlobalTheory.JSW.isRapidInf_colU <;> assumption)
