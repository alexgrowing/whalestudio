import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsValuationSubringAlgClosedNotIsUnit
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuationSubring_algClosed_not_isUnit : ∀ (S : Type) [CommRing S] (u : S), ¬ IsUnit u → ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (V : ValuationSubring L) (f : S →+* ↥V), ¬ IsUnit (f u) ∧ ∀ s ∈ nonZeroDivisors S, f s ≠ 0 := by
  first | exact @GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero | exact GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero | (intros; apply GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero <;> assumption)
