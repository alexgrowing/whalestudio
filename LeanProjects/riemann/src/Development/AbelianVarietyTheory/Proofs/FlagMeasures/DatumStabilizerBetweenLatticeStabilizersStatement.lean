import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DatumStabilizerBetweenLatticeStabilizers
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.datum_stabilizer_between_lattice_stabilizers : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.H0 ⊓ stabL L Λ ≤ S.H0 ⊓ MulAction.stabilizer S.GLV d ∧ ∃ Λ₂ : Submodule L.O S.V, IsLat L Λ₂ ∧ S.H0 ⊓ MulAction.stabilizer S.GLV d ≤ S.H0 ⊓ stabL L Λ₂ := by
  first | exact @GlobalTheory.HL.DatumStab.main | exact GlobalTheory.HL.DatumStab.main | (intros; apply GlobalTheory.HL.DatumStab.main <;> assumption)
