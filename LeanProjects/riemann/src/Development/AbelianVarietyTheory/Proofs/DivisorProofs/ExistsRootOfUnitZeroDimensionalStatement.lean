import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootOfUnitZeroDimensional
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_root_of_unit_zero_dimensional : ∀ (R : Type) [CommRing R] [Ring.KrullDimLE 0 R] (q : ℕ), 0 < q → IsUnit (q : R) → ∀ u : Rˣ, (∀ m : Ideal R, m.IsMaximal → ∃ x : R, x ^ q - (u : R) ∈ m) → ∃ v : Rˣ, v ^ q = u := by
  first | (exact @GlobalTheory.exists_unit_pow_eq_of_krullDimLE_zero) | (exact GlobalTheory.exists_unit_pow_eq_of_krullDimLE_zero) | (intros; apply GlobalTheory.exists_unit_pow_eq_of_krullDimLE_zero  <;> assumption)
