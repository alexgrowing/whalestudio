import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem cechLB_homology_zero_equiv_sections :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y)
      (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), ⨆ i, D i = ⊤ →
      Nonempty ((cechLB f M D).homology 0 ≃ₗ[R] SecOnR f M ⊤) := by
  intro R _ Y f M κ _ _ D hc
  exact ⟨((CochainComplex.isoHomologyπ₀ _).symm ≪≫
      cochainCyclesIsoKer (cechLB f M D) 0 ((cechLB f M D).d 0 1).hom rfl).toLinearEquiv ≪≫ₗ
    (CechOne.kerEquiv M f (fun _ => le_top) hc.ge).symm⟩

end GlobalTheory.AbLaw
