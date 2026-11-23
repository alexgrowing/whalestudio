import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTotallyComplexOfPrimitiveRootThreeLe
import Mathlib
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTotallyComplex_of_primitiveRoot_three_le : ∀ (K : Type) [Field K] [NumberField K] (ζ : K) (m : ℕ), IsPrimitiveRoot ζ m → 3 ≤ m →
    NumberField.IsTotallyComplex K := by
  first | exact @GlobalTheory.tcroot | exact GlobalTheory.tcroot | (intros; apply GlobalTheory.tcroot <;> assumption)
