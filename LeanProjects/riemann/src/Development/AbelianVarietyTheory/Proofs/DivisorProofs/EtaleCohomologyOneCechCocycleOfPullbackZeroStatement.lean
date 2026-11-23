import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyOneCechCocycleOfPullbackZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_one_cechCocycle_of_pullback_zero : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (x : H R (sch.obj X) F 1), pull R (sch.map f) F 1 x = 0 → ∃ s : (free R).obj ((cech f).obj (op (SimplexCategory.mk (1)))) ⟶ F, cobd s = 0 ∧ IsCls s (pull R (cechAug f) F 1 x) := by
  first | exact @GlobalTheory.EtC.LerayOne.cech_cocycle_of_pull_eq_zero | exact GlobalTheory.EtC.LerayOne.cech_cocycle_of_pull_eq_zero | (intros; apply GlobalTheory.EtC.LerayOne.cech_cocycle_of_pull_eq_zero <;> assumption)
