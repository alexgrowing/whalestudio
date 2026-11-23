import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFramesDatumMoveProperties
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDoubleCosetFrames_datum_move_properties : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → s • x ∈ Λ ∧ L.cj s • x ∈ Λ ∧ s • x' ∈ Λ ∧ L.cj s • x' ∈ Λ ∧ (∃ c ∈ L.O, S.h x' x = algebraMap F E S.th * c) ∧ S.h x x = 0 ∧ S.h x' x' = 0 ∧ S.h u x = 0 ∧ S.h u x' = 0 ∧ x ∈ S.X ∧ x' ∈ S.X' := by
  first | exact @GlobalTheory.HL.MoveFacts.move_facts | exact GlobalTheory.HL.MoveFacts.move_facts | (intros; apply GlobalTheory.HL.MoveFacts.move_facts <;> assumption)
