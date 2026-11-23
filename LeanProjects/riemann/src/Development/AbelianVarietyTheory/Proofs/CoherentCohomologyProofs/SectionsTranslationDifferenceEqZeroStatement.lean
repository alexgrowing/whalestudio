import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SectionsTranslationDifferenceEqZero
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_translationDifference_eq_zero : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A), x ≠ η[P.A] → ∀ (σ : LB.Sec (LB.LinComb P.L (K := Fin 2) ![(lift (toUnit P.A ≫ x) (𝟙 P.A) ≫ μ[P.A]).left, 𝟙 P.A.left] ![1, -1])) i, σ.f i = 0 := by
  first | exact @GlobalTheory.sec_translDiff_eq_zero | exact GlobalTheory.sec_translDiff_eq_zero | (intros; apply GlobalTheory.sec_translDiff_eq_zero <;> assumption)
