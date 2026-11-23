import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFramePairCoordinates_transport_innerData : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), Function.Injective c.dat ∧ (∀ g ∈ P.UW0, ∀ d d', LocNG.Datum.Moves g d d' ↔ c.grp g • c.dat d = c.dat d') ∧ (∀ d d', LocNG.Datum.Rel d d' ↔ ∃ h ∈ S.H0, h • c.dat d = c.dat d') ∧ (∀ d g, g ∈ LocNG.Datum.Stab d ↔ c.grp g ∈ S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)) ∧ ∀ d0 d, LocNG.Datum.wt d0 d = invVol (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d0)) (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)) := by
  first | exact @GlobalTheory.HL.CoordDatum.transport | exact GlobalTheory.HL.CoordDatum.transport | (intros; apply GlobalTheory.HL.CoordDatum.transport <;> assumption)
