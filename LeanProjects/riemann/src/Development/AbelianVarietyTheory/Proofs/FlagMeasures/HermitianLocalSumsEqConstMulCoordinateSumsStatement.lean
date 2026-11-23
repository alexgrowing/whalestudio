import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLocalSumsEqConstMulCoordinateSums
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLocalSums_eq_const_mul_coordinateSums : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), ∃ κ : ℝ, 0 ≤ κ ∧ LocNG.sumSq R d0 (LocNG.BBne (H := H)) = ENNReal.ofReal κ * S.ampSq (fun d Λ => ¬ S.BBzero d Λ) ∧ LocNG.sumSq R d0 (fun t => ¬ LocNG.BBne (H := H) t) = ENNReal.ofReal κ * S.ampSq S.BBzero ∧ LocNG.sumSq R d0 (fun _ => True) = ENNReal.ofReal κ * S.ampSq (fun _ _ => True) ∧ LocNG.nn R d0 = ENNReal.ofReal κ * S.nn := by
  first | exact @GlobalTheory.HL.CoordSq.sums_eq | exact GlobalTheory.HL.CoordSq.sums_eq | (intros; apply GlobalTheory.HL.CoordSq.sums_eq <;> assumption)
