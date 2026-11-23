import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HcptPull

theorem fullTorsion_of_dominates : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (n : ℕ), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → FullTorsion G ξ n → FullTorsion G' ξ' n := by
  intro X X' Ω Ω' _ _ ξ ξ' f i G G' _ _ _ _ φ n hd hp hf k _ i' g hg
  have hd' : ξ' ≫ f = spMap i ≫ ξ := hd
  have e : (spMap i' ≫ ξ') ≫ f = spMap (i'.comp i) ≫ ξ := by
    rw [Category.assoc, hd', ← Category.assoc]
    congr 1
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let ρ : (Over.mk (spMap i' ≫ ξ') ⟶ G') →* (Over.mk ((spMap i' ≫ ξ') ≫ f) ⟶ G) :=
    MonoidHom.mk' (pushPt hp.1.w) fun x y => Over.OverMorphism.ext (hp.2 _ x y _ _ rfl rfl).symm
  have ha : (ρ g) ^ n = 1 := by rw [← map_pow, hg, map_one]
  have tr : ∀ {a b : Sp k ⟶ X} (_ : a = b) (u : Over.mk a ⟶ G), u ^ n = 1 →
      ∃ u' : Over.mk b ⟶ G, u'.left = u.left ∧ u' ^ n = 1 := by
    intro a b h u hu
    subst h
    exact ⟨u, rfl, hu⟩
  obtain ⟨u, hl, hu⟩ := tr e (ρ g) ha
  obtain ⟨x, hx⟩ := hf k (i'.comp i) u hu
  have hxw : x.left ≫ G.hom = ξ := by simpa using Over.w x
  have hw : (spMap i ≫ x.left) ≫ G.hom = ξ' ≫ f := by
    rw [Category.assoc, hxw, hd']
  have hs : spMap (i'.comp i) = spMap i' ≫ spMap i := by
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine ⟨Over.homMk (hp.1.lift (spMap i ≫ x.left) ξ' hw) (hp.1.lift_snd _ _ _), ?_⟩
  apply hp.1.hom_ext
  · have h1 : g.left ≫ φ = spMap (i'.comp i) ≫ x.left := by
      rw [← hx, hl]
      rfl
    simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst]
    rw [h1, hs, Category.assoc]
  · have h2 : g.left ≫ G'.hom = spMap i' ≫ ξ' := by simpa using Over.w g
    simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd]
    exact h2

end GlobalTheory.CompanionTheory.Ar.HcptPull
