import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsFiniteGradedModuleLineBundleSections
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_gradedModule_lineBundleSections : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∃ (N : Type) (_ : AddCommGroup N) (_ : Module R N) (_ : Module (MvPolynomial (Fin (m + 1)) R) N) (_ : IsScalarTower R (MvPolynomial (Fin (m + 1)) R) N) (𝒩 : ℤ → Submodule R N) (_ : PolyGradedSMul (Fin (m + 1)) 𝒩) (_ : Decomposition 𝒩), Module.Finite (MvPolynomial (Fin (m + 1)) R) N ∧ ∀ t : ℤ, ∃ φ : grCube (Fin (m + 1)) 𝒩 t ⟶ secCube f (tw M H t) (fun i => nonzeroLocus (s i)), ∀ I : Finset (Fin (m + 1)), I.Nonempty → Function.Bijective (φ.app I).hom := by
  first | exact @GlobalTheory.AbLaw.exists_finite_graded_module_secCube | exact GlobalTheory.AbLaw.exists_finite_graded_module_secCube | (intros; apply GlobalTheory.AbLaw.exists_finite_graded_module_secCube <;> assumption)
