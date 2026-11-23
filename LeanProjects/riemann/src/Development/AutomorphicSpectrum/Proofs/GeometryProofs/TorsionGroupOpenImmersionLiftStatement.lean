import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupOpenImmersionLift
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
theorem _root_.GlobalTheory.T.torsion_group_open_immersion_lift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (N : ℕ) (T : Type) [CommGroup T] (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G (𝟙 _) N i → ∀ (H : Type) [CommGroup H] (Γf : QFGroup R H) (u : Γf.G ⟶ Γ.G) [IsMonHom u], IsOpenImmersion u.left → (∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ Set.range u.left) → ∃ v : Γf.G ⟶ G, v.left = u.left ≫ i ∧ IsMonHom v ∧ Mono v ∧ ∀ e, IsPullback ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map v) (toUnit _) ((𝟙 (thickObj R (IsLocalRing.maximalIdeal R) e G)) ^ N) η[thickObj R (IsLocalRing.maximalIdeal R) e G] := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.FinPart.finite_part_torsion | exact GlobalTheory.CompanionTheory.Ar.BT.FinPart.finite_part_torsion | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.FinPart.finite_part_torsion <;> assumption)
