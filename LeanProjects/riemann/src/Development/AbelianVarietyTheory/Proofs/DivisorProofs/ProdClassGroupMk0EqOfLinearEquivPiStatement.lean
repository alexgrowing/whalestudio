import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdClassGroupMk0EqOfLinearEquivPi
import Mathlib
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_classGroup_mk0_eq_of_linearEquiv_pi : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (ι : Type) [Fintype ι] (I J : ι → (Ideal R)⁰), Nonempty (((i : ι) → (I i : Ideal R)) ≃ₗ[R] ((i : ι) → (J i : Ideal R))) → ∏ i, ClassGroup.mk0 (I i) = ∏ i, ClassGroup.mk0 (J i) := by
  first | exact @GlobalTheory.prod_classGroup_mk0_eq_of_pi_linearEquiv | exact GlobalTheory.prod_classGroup_mk0_eq_of_pi_linearEquiv | (intros; apply GlobalTheory.prod_classGroup_mk0_eq_of_pi_linearEquiv <;> assumption)
