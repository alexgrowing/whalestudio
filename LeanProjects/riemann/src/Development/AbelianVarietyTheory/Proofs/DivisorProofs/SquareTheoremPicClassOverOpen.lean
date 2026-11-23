import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfSquareCechPicardTranslatesStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SquareOpen

theorem pull_mul_add_pull_mul_inv_of_opens : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (c : Pic (A.hom ⁻¹ᵁ U).toScheme) (Y : Over S) (l : (Y ⟶ A) → (Y.left ⟶ (A.hom ⁻¹ᵁ U).toScheme)), (∀ y, Y.hom y ∈ U) → (∀ p, l p ≫ (A.hom ⁻¹ᵁ U).ι = p.left) → ∀ x a : Y ⟶ A, GlobalTheory.CechPic.pull (l (x * a)) c + GlobalTheory.CechPic.pull (l (x * a⁻¹)) c = 2 • GlobalTheory.CechPic.pull (l (x)) c + GlobalTheory.CechPic.pull (l (a)) c + GlobalTheory.CechPic.pull (l (a⁻¹)) c - 2 • GlobalTheory.CechPic.pull (l ((1 : Y ⟶ A))) c := by
  intro S _ A _ hA U c Y l hY hl x a
  let A' := (Over.pullback U.ι).obj A
  have hA' : IsAbelianScheme A' := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback U.ι A hA
  have h := isGrpPullback_pullback A U.ι
  let e := (isPullback_morphismRestrict A.hom U).flip.isoPullback
  have he : e.inv ≫ (A.hom ⁻¹ᵁ U).ι = pullback.fst A.hom U.ι := by
    rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_fst]
  have hrange : Set.range Y.hom.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [U.range_ι]
    exact hY y
  let Y' : Over U.toScheme := Over.mk (IsOpenImmersion.lift U.ι Y.hom hrange)
  have hY' : Y'.hom ≫ U.ι = Y.hom := IsOpenImmersion.lift_fac _ _ _
  let τ : Over.mk (Y'.hom ≫ U.ι) ⟶ Y := Over.homMk (𝟙 Y.left) (by erw [Category.id_comp]; exact hY'.symm)
  have lift : ∀ p : Y ⟶ A, ∃ p' : Y' ⟶ A', pushHom h Y' p' = τ ≫ p := by
    intro p
    refine ⟨Over.homMk (pullback.lift p.left Y'.hom (by rw [Over.w p, hY'])) (by
      exact pullback.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    simp only [pushHom, pushPt, τ, MonoidHom.mk'_apply, Over.homMk_left, Over.comp_left]
    rw [pullback.lift_fst]
    exact (Category.id_comp _).symm
  have key : ∀ (p : Y ⟶ A) (p' : Y' ⟶ A'), pushHom h Y' p' = τ ≫ p → l p = p'.left ≫ e.inv := by
    intro p p' hp
    rw [← cancel_mono (A.hom ⁻¹ᵁ U).ι, hl, Category.assoc, he]
    have := congrArg (fun q => q.left) hp
    simp only [pushHom, pushPt, τ, MonoidHom.mk'_apply, Over.homMk_left, Over.comp_left] at this
    exact (Category.id_comp _).symm.trans this.symm
  obtain ⟨x', hx⟩ := lift x
  obtain ⟨a', ha⟩ := lift a
  have hmul : pushHom h Y' (x' * a') = τ ≫ (x * a) := by
    rw [map_mul, hx, ha, MonObj.comp_mul]
  have hainv : pushHom h Y' a'⁻¹ = τ ≫ a⁻¹ := by
    rw [map_inv, ha, GrpObj.comp_inv]
  have hinv : pushHom h Y' (x' * a'⁻¹) = τ ≫ (x * a⁻¹) := by
    rw [map_mul, hainv, hx, MonObj.comp_mul]
  have hone : pushHom h Y' 1 = τ ≫ 1 := by
    rw [map_one, MonObj.comp_one]
  rw [key _ _ hmul, key _ _ hinv, key _ _ hx, key _ _ ha, key _ _ hainv, key _ _ hone]
  simp only [pull_comp]
  exact GlobalTheory.T.theorem_of_square_cechPicard_translates U.toScheme A' hA' (pull e.inv c) Y' x' a'

end GlobalTheory.SquareOpen
