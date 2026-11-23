import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallResidueFieldFunctional
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_forall_residueField_functional' : ∀ (A M : Type) [CommRing A] [IsReduced A] [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M] (x : M), (∀ (p : Ideal A) [p.IsPrime] (l : M →ₗ[A] p.ResidueField), l x = 0) → x = 0 := by
  first | exact @GlobalTheory.eq_zero_of_forall_residueField_functional | exact GlobalTheory.eq_zero_of_forall_residueField_functional | (intros; apply GlobalTheory.eq_zero_of_forall_residueField_functional <;> assumption)
