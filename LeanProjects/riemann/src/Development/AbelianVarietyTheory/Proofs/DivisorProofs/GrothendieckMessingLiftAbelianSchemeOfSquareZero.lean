import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfNilpotentReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsAbelianSchemeSmoothLiftNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLiftSmoothNilpotentThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftShearMapSquareZeroAbelianSchemesStatement

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem liftObj_sq : AbelianDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π → LiftObj (divided₂ hI) π := by
  intro P R R₀ _ _ I hI π hπ hk H g A₀ _ A' _ i' h' hA' hg' F hF
  have hn : IsNilpotent (RingHom.ker π) := ⟨2, hk ▸ hI⟩
  obtain ⟨X, i, h, hX, hFil⟩ := H.exists_lift h' hA' hg' hF
  have hA₀ : IsAbelianScheme A₀ := PolPull.isAbelianScheme_of_isGrpPullback hA' h'
  have hg₀ : SmoothOfRelativeDimension g A₀.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h'.1 hg'
  obtain ⟨e, he, he₀⟩ := GlobalTheory.T.exists_section_lift_smooth_nilpotent_thickening R R₀ π hπ hn X A₀ i h hX (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left
    (Over.w (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀))
  have w : ((fst A₀ A₀).left ≫ i) ≫ X.hom = ((snd A₀ A₀).left ≫ i) ≫ X.hom := by
    rw [Category.assoc, Category.assoc, h.w, Over.w_assoc, Over.w_assoc]
  have hl₁ : (Limits.pullback.lift _ _ w : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left) ≫ (fst X X).left
      = (fst A₀ A₀).left ≫ i := Limits.pullback.lift_fst _ _ _
  have hl₂ : (Limits.pullback.lift _ _ w : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left) ≫ (snd X X).left
      = (snd A₀ A₀).left ≫ i := Limits.pullback.lift_snd _ _ _
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_lift_shearMap_squareZero_abelianSchemes R R₀ I hI π hπ hk H g g A₀ A₀ A' A' i' i' h' h' hA' hA' hg' hg' X X i i h h hX hX
    e e he he he₀ he₀ _ hl₁ hl₂ (𝟙 A₀) (fun d hd ↦ by rw [push_id]; exact hd)
  have hμ : (fst A₀ A₀ ≫ 𝟙 A₀) * snd A₀ A₀ = μ[A₀] := by
    rw [Category.comp_id, Hom.mul_def, lift_fst_snd, Category.id_comp]
  rw [hμ] at hm
  obtain ⟨_, hp, hab⟩ := GlobalTheory.T.exists_grpObj_isAbelianScheme_smoothLift_nilpotent R R₀ π hπ hn A₀ hA₀ X i h hX e he he₀ _ hl₁ hl₂ m hm
  have hg : SmoothOfRelativeDimension g X.hom := GlobalTheory.T.smoothOfRelativeDimension_of_nilpotent_reduction R R₀ π hπ hn g X A₀ i h hX hg₀
  exact ⟨X, _, i, hp, hab, hg, (schemeFil_eq_liftFil _ hp (P.1 R X g hab hg).1).symm.trans hFil⟩

end GlobalTheory.SqLift
