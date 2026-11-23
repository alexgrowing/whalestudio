import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameCoordinatesTransportInnerLattices
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFrameCoordinates_transport_innerLattices : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), Function.Injective (c.inn P.A.f) ∧ (∀ L, P.A.IsInner L ↔ S.IsInner S.f S.es (c.inn P.A.f L)) ∧ (∀ A, S.IsInner S.f S.es A → ∃ L, A = c.inn P.A.f L) ∧ ∀ L, c.lat (P.A.LamStd L) = S.stdLat S.f S.es (c.inn P.A.f L) := by
  first | exact @GlobalTheory.HL.CoordInnerFst.transport | exact GlobalTheory.HL.CoordInnerFst.transport | (intros; apply GlobalTheory.HL.CoordInnerFst.transport <;> assumption)
