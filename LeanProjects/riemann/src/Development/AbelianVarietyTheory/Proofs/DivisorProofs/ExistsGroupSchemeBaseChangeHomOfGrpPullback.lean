import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.GrpBC

theorem exists_baseChange_hom : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G A : Over S) [GrpObj G] [GrpObj A] (G' A' : Over S') [GrpObj G'] [GrpObj A'] (φG : G'.left ⟶ G.left) (φA : A'.left ⟶ A.left) (p : G ⟶ A), IsGrpPullback G' G f φG → IsGrpPullback A' A f φA → IsMonHom p → ∃ p' : G' ⟶ A', IsMonHom p' ∧ p'.left ≫ φA = φG ≫ p.left := by
  intro S S' f G A _ _ G' A' _ _ φG φA p hG hA hp
  have w : (φG ≫ p.left) ≫ A.hom = G'.hom ≫ f := by
    rw [Category.assoc, Over.w p, hG.1.w]
  have hq1 : hA.1.lift (φG ≫ p.left) G'.hom w ≫ φA = φG ≫ p.left := hA.1.lift_fst _ _ _
  have hq2 : hA.1.lift (φG ≫ p.left) G'.hom w ≫ A'.hom = G'.hom := hA.1.lift_snd _ _ _
  let p' : G' ⟶ A' := Over.homMk (hA.1.lift (φG ≫ p.left) G'.hom w) hq2
  have hp' : p'.left ≫ φA = φG ≫ p.left := hq1
  refine ⟨p', GlobalTheory.Serre.isMonHom_of_mul_comp p' fun T x y => ?_, hp'⟩
  apply Over.OverMorphism.ext
  apply hA.1.hom_ext
  · have e1 := hG.2 T x y (pushPt hG.1.w x) (pushPt hG.1.w y) rfl rfl
    have e2 := hA.2 T (x ≫ p') (y ≫ p') (pushPt hG.1.w x ≫ p) (pushPt hG.1.w y ≫ p)
      (by simp only [Over.comp_left, pushPt, Over.homMk_left, Category.assoc, hp'])
      (by simp only [Over.comp_left, pushPt, Over.homMk_left, Category.assoc, hp'])
    have e3 : (pushPt hG.1.w x ≫ p * pushPt hG.1.w y ≫ p).left = (x * y).left ≫ φG ≫ p.left := by
      rw [← MonObj.mul_comp, Over.comp_left, e1, Category.assoc]
    rw [← e2, e3, Over.comp_left, Category.assoc, hp']
  · rw [Over.w, Over.w]

end GlobalTheory.GrpBC
