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

namespace GlobalTheory.CompanionTheory.Ar.BT.RatKer

theorem exists_section_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (H : Type) [CommGroup H] (Γf : QFGroup R H) (A E : Over (Spec (CommRingCat.of R))) (a : A ⟶ Γf.G) (b : Γf.G ⟶ E) (e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ E), IsClosedImmersion a.left → IsPullback a (toUnit A) b e → ∀ g : A.left, (A.hom g).asIdeal = ⊥ → ∃ (κ : genPt R ⟶ A) (x : Spec (CommRingCat.of (FractionRing R))), κ.left x = g := by
  intro R _ _ H _ Γf A E a b e ha hP g hg
  have hwa : Γf.G.hom (a.left g) = A.hom g := by
    rw [← Scheme.Hom.comp_apply, Over.w]
  obtain ⟨t, x, hx⟩ := Γf.11 (a.left g) (by rw [hwa]; exact hg)
  have hgen : (GlobalTheory.CompanionTheory.Ar.BT.genPt R).hom x = A.hom g := by
    rw [← Over.w (Γf.9 t), Scheme.Hom.comp_apply, hx, hwa]
  have hab := congrArg (fun φ => φ.left g) hP.w
  simp only [Over.comp_left, Scheme.Hom.comp_apply, Over.toUnit_left] at hab
  have hpt : Γf.9 t ≫ b = toUnit (GlobalTheory.CompanionTheory.Ar.BT.genPt R) ≫ e := by
    apply Over.OverMorphism.ext
    apply GlobalTheory.CompanionTheory.Ar.BT.Tors.eq_of_same_point E.hom _ _ (Over.w _) (Over.w _) x x
    simp only [Over.comp_left, Scheme.Hom.comp_apply, Over.toUnit_left]
    rw [hx, hab, hgen]
  refine ⟨hP.lift (Γf.9 t) (toUnit _) hpt, x, ?_⟩
  apply a.left.isClosedEmbedding.injective
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hP.lift_fst, hx]

end GlobalTheory.CompanionTheory.Ar.BT.RatKer
