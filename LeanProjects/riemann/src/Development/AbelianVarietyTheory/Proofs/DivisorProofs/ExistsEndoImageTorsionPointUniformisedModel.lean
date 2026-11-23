import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EndoPt

theorem exists_mulEquiv_points {S S' : Scheme.{0}} {g : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G g φ) (T : Over S') :
    ∃ E : (T ⟶ G') ≃* (Over.mk (T.hom ≫ g) ⟶ G), ∀ x, (E x).left = x.left ≫ φ := by
  let F : (T ⟶ G') → (Over.mk (T.hom ≫ g) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      change (x.left ≫ φ) ≫ G.hom = T.hom ≫ g
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x])
  have hF : ∀ x, (F x).left = x.left ≫ φ := fun x => rfl
  have inj : Function.Injective F := fun x y e => by
    apply Over.OverMorphism.ext
    refine h.1.hom_ext ?_ ?_
    · rw [← hF, ← hF, e]
    · rw [Over.w x, Over.w y]
  have sur : Function.Surjective F := fun z => by
    have w : z.left ≫ G.hom = T.hom ≫ g := Over.w z
    refine ⟨Over.homMk (h.1.lift z.left T.hom w) (h.1.lift_snd _ _ w), ?_⟩
    apply Over.OverMorphism.ext
    exact h.1.lift_fst _ _ w
  refine ⟨{ Equiv.ofBijective F ⟨inj, sur⟩ with map_mul' := fun x y => ?_ }, hF⟩
  apply Over.OverMorphism.ext
  exact (h.2 T x y (F x) (F y) rfl rfl).symm

theorem exists_point_of_isMonHom {S S' : Scheme.{0}} {g : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G g φ) (f : G ⟶ G) [IsMonHom f] (m : ℕ) {T : Over S'}
    (x : T ⟶ G') (hx : x ^ m = 1) :
    ∃ x₂ : T ⟶ G', x₂.left ≫ φ = x.left ≫ φ ≫ f.left ∧ x₂ ^ m = 1 := by
  obtain ⟨E, hE⟩ := exists_mulEquiv_points h T
  refine ⟨E.symm (E x ≫ f), ?_, ?_⟩
  · rw [← hE, MulEquiv.apply_symm_apply, Over.comp_left, hE, Category.assoc]
  · rw [← map_pow, ← MonObj.pow_comp, ← map_pow, hx, map_one, MonObj.one_comp, map_one]

theorem exists_endo_point : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (f : ρ.P.A ⟶ ρ.P.A), IsMonHom f → ∀ (m : ℕ) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x ^ m = 1 → ∃ x₂ : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, x₂.left ≫ u.φ = x.left ≫ u.φ ≫ f.left ∧ x₂ ^ m = 1 := by
  intro o Ω _ _ _ S ρ p _ y₀ u f hf m x hx
  exact exists_point_of_isMonHom u.cart f m x hx

end GlobalTheory.EndoPt
