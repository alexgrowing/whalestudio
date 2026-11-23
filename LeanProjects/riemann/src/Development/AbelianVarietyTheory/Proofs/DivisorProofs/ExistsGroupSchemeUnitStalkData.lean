import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

noncomputable section

namespace GlobalTheory.Nef

theorem exists_stalk_fac {X : Scheme.{0}} (x : X) {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ X)
    (h : f (IsLocalRing.closedPoint R) = x) :
    ∃ φ : X.presheaf.stalk x ⟶ R, Spec.map φ ≫ X.fromSpecStalk x = f := by
  subst h
  exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩

theorem exists_stalk_map {X Y : Scheme.{0}} (x : X) (g : X ⟶ Y) (y : Y) (hy : g x = y) :
    ∃ φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x, Spec.map φ ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ g := by
  subst hy
  exact exists_stalk_fac (g x) (X.fromSpecStalk x ≫ g) (congrArg (fun z => g z) Scheme.fromSpecStalk_closedPoint)

theorem stalk_hom_eq {X : Scheme.{0}} (x : X) {R : CommRingCat.{0}} (φ ψ : X.presheaf.stalk x ⟶ R)
    (h : Spec.map φ ≫ X.fromSpecStalk x = Spec.map ψ ≫ X.fromSpecStalk x) : φ = ψ :=
  Spec.map_injective ((cancel_mono (X.fromSpecStalk x)).1 h)

section

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

theorem unitSec_sqr : unitSec G ≫ sqr G = unitSec G := by
  have h1 : (1 : 𝟙_ (Over S) ⟶ G) = η[G] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have h2 : η[G] ≫ (𝟙 G * 𝟙 G) = η[G] := by
    rw [Hom.mul_def, ← Category.assoc, comp_lift, Category.comp_id, ← Hom.mul_def, ← h1, _root_.one_mul]
  change η[G].left ≫ (𝟙 G * 𝟙 G : G ⟶ G).left = η[G].left
  rw [← Over.comp_left, h2]

theorem sqr_hom : sqr G ≫ G.hom = G.hom := Over.w _

end

theorem stalkData_exists : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ s : S, ∃ π ε m,
    StalkData G s π ε m ∧ ε.comp π = RingHom.id _ ∧ m.comp π = π ∧ ε.comp m = ε := by
  intro S G _ s
  obtain ⟨π, hπ⟩ := exists_stalk_map (unitSec G s) G.hom s (by
    rw [← Scheme.Hom.comp_apply, sec_hom]; rfl)
  obtain ⟨ε, hε⟩ := exists_stalk_map s (unitSec G) (unitSec G s) rfl
  obtain ⟨m, hm⟩ := exists_stalk_map (unitSec G s) (sqr G) (unitSec G s) (by
    rw [← Scheme.Hom.comp_apply, unitSec_sqr])
  refine ⟨π.hom, ε.hom, m.hom, ⟨hπ, hε, hm⟩, ?_, ?_, ?_⟩
  · have : π ≫ ε = 𝟙 _ := stalk_hom_eq s _ _ (by
      rw [Spec.map_comp, Category.assoc, hπ, ← Category.assoc, hε, Category.assoc, sec_hom,
        Category.comp_id, Spec.map_id, Category.id_comp])
    exact congrArg CommRingCat.Hom.hom this
  · have : π ≫ m = π := stalk_hom_eq s _ _ (by
      rw [Spec.map_comp, Category.assoc, hπ, ← Category.assoc, hm, Category.assoc, sqr_hom])
    exact congrArg CommRingCat.Hom.hom this
  · have : m ≫ ε = ε := stalk_hom_eq (unitSec G s) _ _ (by
      rw [Spec.map_comp, Category.assoc, hm, ← Category.assoc, hε, Category.assoc, unitSec_sqr])
    exact congrArg CommRingCat.Hom.hom this

end GlobalTheory.Nef
