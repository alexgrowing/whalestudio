import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstLift

theorem isGrpPullback_of_eq_id {S : Scheme.{0}} (G : Over S) [GrpObj G] {f : S ⟶ S} {φ : G.left ⟶ G.left}
    (hf : f = 𝟙 S) (hφ : φ = 𝟙 _) : IsGrpPullback G G f φ := by
  subst hf hφ
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (mul_left_congr (Category.comp_id T.hom) x₀ y₀ x y (hx.trans (Category.comp_id _))
    (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm

theorem exists_constLift : ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ →
    SmoothOfRelativeDimension g A₀.hom → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ),
    (∀ a : ℂ, π (algebraMap ℂ D a) = a) →
    ∃ (A' : Over (Sp D)) (_ : GrpObj A') (q : A'.left ⟶ A₀.left) (i : A₀.left ⟶ A'.left),
      IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom ∧ IsGrpPullback A' A₀ (spMap (algebraMap ℂ D)) q ∧
        IsGrpPullback A₀ A' (spMap π) i ∧ i ≫ q = 𝟙 _ := by
  intro A₀ _ g h hg D _ _ π hπ
  have e : spMap π ≫ spMap (algebraMap ℂ D) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, show π.comp (algebraMap ℂ D) = RingHom.id ℂ from RingHom.ext hπ,
      CommRingCat.ofHom_id, Spec.map_id]
  have w : 𝟙 A₀.left ≫ A₀.hom = (A₀.hom ≫ spMap π) ≫ spMap (algebraMap ℂ D) := by
    rw [Category.assoc, e, Category.id_comp, Category.comp_id]
  have hq := isGrpPullback_pullback A₀ (spMap (algebraMap ℂ D))
  refine ⟨(Over.pullback (spMap (algebraMap ℂ D))).obj A₀, inferInstance,
    pullback.fst A₀.hom (spMap (algebraMap ℂ D)), pullback.lift _ _ w, ?_, ?_, hq, ?_, pullback.lift_fst _ _ w⟩
  · exact
      { comm := by have := h.comm; infer_instance
        smooth := by have := h.smooth; change Smooth (pullback.snd A₀.hom _); infer_instance
        proper := by have := h.proper; change IsProper (pullback.snd A₀.hom _); infer_instance
        geomConnected := by
          have := h.geomConnected; change GeometricallyConnected (pullback.snd A₀.hom _); infer_instance }
  · change SmoothOfRelativeDimension g (pullback.snd A₀.hom _)
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback
      (IsPullback.of_hasPullback A₀.hom _) hg
  · exact hq.cancel (isGrpPullback_of_eq_id A₀ e (pullback.lift_fst _ _ w)) (pullback.lift_snd _ _ w)

end GlobalTheory.ConstLift
