import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeCountBoundFrames
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_count_bound_frames : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ C, S.IsCls C → ∀ p ∈ C, 0 ≤ S.a → ({Mh : Submodule L.O S.V | S.Mof p.1 p.2 ≤ Mh ∧ (∀ x ∈ Mh, x ∈ S.ME) ∧ ∀ x ∈ Mh, ∀ y ∈ Mh, S.h x y ∈ L.O}.encard : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2)) := by
  first | exact @GlobalTheory.FrameOver.encard_overlattices_le | exact GlobalTheory.FrameOver.encard_overlattices_le | (intros; apply GlobalTheory.FrameOver.encard_overlattices_le <;> assumption)
