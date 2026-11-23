import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddValuationNonnegRingOfIntegersNumberField
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addValuation_nonneg_ringOfIntegers_numberField : ∀ (L : Type) [Field L] [NumberField L] (v : AddValuation L (WithTop ℤ)) (a : 𝓞 L), 0 ≤ v (a : L) := by
  first | exact @GlobalTheory.addValuation_nonneg_of_ringOfIntegers | exact GlobalTheory.addValuation_nonneg_of_ringOfIntegers | (intros; apply GlobalTheory.addValuation_nonneg_of_ringOfIntegers <;> assumption)
