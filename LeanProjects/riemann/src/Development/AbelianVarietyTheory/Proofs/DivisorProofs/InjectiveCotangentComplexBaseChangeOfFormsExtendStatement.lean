import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveCotangentComplexBaseChangeOfFormsExtend
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_cotangentComplexBaseChange_of_forms_extend' : ∀ (A P R K : Type) [CommRing A] [CommRing P] [CommRing R] [Field K] [Algebra A P] [Algebra A R] [Algebra P R] [IsScalarTower A P R] [Algebra R K] [Algebra P K] [IsScalarTower P R K] [Algebra A K] [IsScalarTower A P K], (∀ ℓ : RingHom.ker (algebraMap P R) →ₗ[P] K, ∃ D : Derivation A P K, ∀ i : RingHom.ker (algebraMap P R), D i = ℓ i) → Function.Injective (KaehlerDifferential.cotangentComplexBaseChange A R P K) := by
  first | exact @GlobalTheory.injective_cotangentComplexBaseChange_of_forms_extend | exact GlobalTheory.injective_cotangentComplexBaseChange_of_forms_extend | (intros; apply GlobalTheory.injective_cotangentComplexBaseChange_of_forms_extend <;> assumption)
