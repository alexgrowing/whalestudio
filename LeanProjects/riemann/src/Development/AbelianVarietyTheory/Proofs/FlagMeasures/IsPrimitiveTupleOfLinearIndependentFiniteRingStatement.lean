import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrimitiveTupleOfLinearIndependentFiniteRing
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrimitiveTuple_of_linearIndependent_finite_ring : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (χ : AddChar B ℂ), χ.IsPrimitive → ∀ (k n : ℕ) (x : Fin k → Fin n → B), (∀ s : Fin k → B, ∑ a, s a • x a = 0 → s = 0) → Prim c x := by
  first | exact @GlobalTheory.GramCount.prim_of_indep_of_isPrimitive | exact GlobalTheory.GramCount.prim_of_indep_of_isPrimitive | (intros; apply GlobalTheory.GramCount.prim_of_indep_of_isPrimitive <;> assumption)
