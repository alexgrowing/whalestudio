import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformizationThickeningCompat
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
theorem _root_.GlobalTheory.T.uniformization_thickening_compat : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ), thickMap R I e (splitTorus (Spec (CommRingCat.of R)) D.toPre.X) ≫ (GlobalTheory.Diag.baseChangeIso (thick R I (e + 1)) D.toPre.X).hom.left ≫ (U.gt (e + 1)).i.left = (GlobalTheory.Diag.baseChangeIso (thick R I e) D.toPre.X).hom.left ≫ (U.gt e).i.left ≫ thickMap R I e G := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.GtI.gt_i | exact GlobalTheory.CompanionTheory.Ar.BT.GtI.gt_i | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.GtI.gt_i <;> assumption)
