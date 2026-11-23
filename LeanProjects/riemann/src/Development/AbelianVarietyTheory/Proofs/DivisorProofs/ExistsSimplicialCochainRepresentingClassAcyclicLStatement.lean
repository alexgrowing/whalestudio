import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimplicialCochainRepresentingClassAcyclicL
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_simplicialCochain_representing_class_acyclicLevels : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ), (∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op (SimplexCategory.mk (k))))) F m, y = 0) → ∀ x : H R E F n, ∃ s : (free R).obj (E.obj (op (SimplexCategory.mk (n)))) ⟶ F, cobd s = 0 ∧ IsCls s x := by
  first | (exact @GlobalTheory.EtC.leray_surj) | (exact GlobalTheory.EtC.leray_surj) | (intros; apply GlobalTheory.EtC.leray_surj <;> assumption)
