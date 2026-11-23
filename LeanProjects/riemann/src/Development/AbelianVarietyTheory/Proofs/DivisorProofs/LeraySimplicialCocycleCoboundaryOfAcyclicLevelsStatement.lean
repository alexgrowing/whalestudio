import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeraySimplicialCocycleCoboundaryOfAcyclicLevels
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leray_simplicialCocycle_coboundary_of_acyclicLevels : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ), (∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op (SimplexCategory.mk (k))))) F m, y = 0) → (∀ s : (free R).obj (E.obj (op (SimplexCategory.mk (0)))) ⟶ F, IsCls s 0 → s = 0) ∧ ∀ s : (free R).obj (E.obj (op (SimplexCategory.mk (n + 1)))) ⟶ F, IsCls s 0 → ∃ t : (free R).obj (E.obj (op (SimplexCategory.mk (n)))) ⟶ F, cobd t = s := by
  first | (exact @GlobalTheory.EtC.leray_inj) | (exact GlobalTheory.EtC.leray_inj) | (intros; apply GlobalTheory.EtC.leray_inj <;> assumption)
