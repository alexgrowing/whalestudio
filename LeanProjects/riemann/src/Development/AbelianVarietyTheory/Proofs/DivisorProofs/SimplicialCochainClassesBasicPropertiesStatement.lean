import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicProperties
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simplicialCochain_classes_basic_properties : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ), (∀ s : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F, cobd s = 0 → ∃ x : H R E F n, IsCls s x) ∧ (∀ (s s' : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F) (x x' : H R E F n), IsCls s x → IsCls s' x' → IsCls (s + s') (x + x')) ∧ (∀ (s : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F) (x x' : H R E F n), IsCls s x → IsCls s x' → x = x') ∧ (∀ (t : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F) (x : H R E F ((n + 1 : ℕ) : ℤ)), IsCls (cobd t) x → x = 0) ∧ ∀ (E' : Spc) (f : E' ⟶ E) (s : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F) (x : H R E F n), IsCls s x → IsCls ((free R).map (f.app (op (SimplexCategory.mk n))) ≫ s) (pull R f F n x) := by
  first | exact @GlobalTheory.EtC.isCls_basic | exact GlobalTheory.EtC.isCls_basic | (intros; apply GlobalTheory.EtC.isCls_basic <;> assumption)
