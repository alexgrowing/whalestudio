import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairChangedDualVectors
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framePair_changed_dualVectors : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : WCoord P S), ∃ (P₂ : LocNG.FPair H r) (c₂ : Coord P₂ S) (φ : LocNG.Datum P ≃ LocNG.Datum P₂), c₂.e = c.e ∧ P₂.St = P.St ∧ P₂.K0 = P.K0 ∧ P₂.UW0 = P.UW0 ∧ P₂.Hp = P.Hp ∧ (P₂.PrimeTo ↔ P.PrimeTo) ∧ (∀ d, c₂.dat (φ d) = c.dat d) ∧ (∀ d t, LocNG.IsTermOver P d t ↔ LocNG.IsTermOver P₂ (φ d) t) ∧ (∀ d t, LocNG.IsTermOver P d t → LocNG.om P₂ t = LocNG.om P t) ∧ ∀ g d d', LocNG.Datum.Moves g d d' ↔ LocNG.Datum.Moves g (φ d) (φ d') := by
  first | exact @GlobalTheory.HL.ToC.changed_duals | exact GlobalTheory.HL.ToC.changed_duals | (intros; apply GlobalTheory.HL.ToC.changed_duals <;> assumption)
