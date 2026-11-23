import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBasisCongrLevelMod
import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplectic_basis_congr_level_mod : ∀ (h k : ℕ) (M : Type) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] (Ef : LinearMap.BilinForm ℤ M) (l : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] M), 0 < k → Module.finrank ℤ M = 2 * h → (∀ x, Ef x x = 0) → Function.Bijective Ef → (∀ a b, (k : ℤ) ∣ Ef (l a) (l b) - omegaStd a b) → ∃ B : (Fin h ⊕ Fin h → ℤ) ≃ₗ[ℤ] M, (∀ a b, Ef (B a) (B b) = omegaStd a b) ∧ ∀ a, ∃ m : M, l a - B a = (k : ℤ) • m := by
  first | exact @GlobalTheory.SymplecticLevelLift.exists_symplectic_equiv_congr | exact GlobalTheory.SymplecticLevelLift.exists_symplectic_equiv_congr | (intros; apply GlobalTheory.SymplecticLevelLift.exists_symplectic_equiv_congr <;> assumption)
