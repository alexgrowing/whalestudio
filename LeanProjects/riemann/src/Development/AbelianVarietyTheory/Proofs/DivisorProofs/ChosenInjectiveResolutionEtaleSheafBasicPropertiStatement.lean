import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafBasicProperti
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ n : ℤ, Injective ((res R F).X n)) ∧ (∀ n : ℤ, n < 0 → IsZero ((res R F).X n)) ∧ Mono (resι R F) ∧ (∃ w : resι R F ≫ (res R F).d 0 1 = 0, (ShortComplex.mk _ _ w).Exact) ∧ (∀ n : ℤ, n ≠ 0 → (res R F).ExactAt n) ∧ ∀ (E : Spc) (n : ℤ), 0 < n → IsZero (((chains R).obj E).X n) := by
  first | exact @GlobalTheory.EtC.res_basic | exact GlobalTheory.EtC.res_basic | (intros; apply GlobalTheory.EtC.res_basic <;> assumption)
