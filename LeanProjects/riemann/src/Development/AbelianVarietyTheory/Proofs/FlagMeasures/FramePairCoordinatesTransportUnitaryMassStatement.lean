import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMass
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framePairCoordinates_transport_unitary_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), (∀ g, g ∈ P.UW0 ↔ c.grp g ∈ S.H0) ∧ (∀ g, g ∈ P.K0 ↔ c.grp g ∈ S.K0) ∧ Function.Bijective c.lat ∧ (∀ g Λ, c.lat (LocNG.img g Λ) = c.grp g • c.lat Λ) ∧ (∀ g Λ, g ∈ LocNG.Aut Λ ↔ c.grp g ∈ MulAction.stabilizer S.GLV (c.lat Λ)) ∧ ∀ t : Term V M r, LocNG.mu P t = S.mu (c.lat t.abelian₂) := by
  first | exact @GlobalTheory.HL.CoordMass.transport | exact GlobalTheory.HL.CoordMass.transport | (intros; apply GlobalTheory.HL.CoordMass.transport <;> assumption)
