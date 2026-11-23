import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrallyClosedFiniteDedekindClassFinite
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrally_closed_finite_dedekind_class_finite : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] [Module.Finite ℤ A],
    IsDedekindDomain A ∧ Finite (ClassGroup A) := by
  first | exact @GlobalTheory.IntClosedOrder.isDedekindDomain_and_finite_classGroup | exact GlobalTheory.IntClosedOrder.isDedekindDomain_and_finite_classGroup | (intros; apply GlobalTheory.IntClosedOrder.isDedekindDomain_and_finite_classGroup <;> assumption)
