import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsOfClosedSubgroup
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_points_of_closed_subgroup : ∀ (R : Type) [CommRing R] [IsDomain R] (H : Type) [CommGroup H] (Γf : QFGroup R H) (A E : Over (Spec (CommRingCat.of R))) (a : A ⟶ Γf.G) (b : Γf.G ⟶ E) (e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ E), IsClosedImmersion a.left → IsPullback a (toUnit A) b e → ∀ g : A.left, (A.hom g).asIdeal = ⊥ → ∃ (κ : genPt R ⟶ A) (x : Spec (CommRingCat.of (FractionRing R))), κ.left x = g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.RatKer.exists_section_of_generic | exact GlobalTheory.CompanionTheory.Ar.BT.RatKer.exists_section_of_generic | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.RatKer.exists_section_of_generic <;> assumption)
