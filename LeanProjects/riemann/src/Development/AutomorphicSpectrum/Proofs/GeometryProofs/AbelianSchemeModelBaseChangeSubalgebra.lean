import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem model_passes_to_subalgebra : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (A : Over (Sp V)) [GrpObj A] (A₀ : Over (Sp k)) [GrpObj A₀] (φ : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap (algebraMap k V)) φ → ∀ R : Subalgebra k V, ∃ (_ : GrpObj (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R))))) (φ₁ : A.left ⟶ pullback A₀.hom (spMap (algebraMap k R))), IsGrpPullback (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) A₀ (spMap (algebraMap k R)) (pullback.fst _ _) ∧ IsGrpPullback A (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) (spMap R.val.toRingHom) φ₁ ∧ φ₁ ≫ pullback.fst _ _ = φ := by
  intro k V _ _ _ A _ A₀ _ φ h R
  have es : spMap R.val.toRingHom ≫ spMap (algebraMap k R) = spMap (algebraMap k V) := by
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have w : φ ≫ A₀.hom = (A.hom ≫ spMap R.val.toRingHom) ≫ spMap (algebraMap k R) := by
    rw [Category.assoc, es]; exact h.1.w
  let inst : GrpObj (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) :=
    inferInstanceAs (GrpObj ((Over.pullback (spMap (algebraMap k R))).obj A₀))
  have h₁ : IsGrpPullback (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) A₀ (spMap (algebraMap k R))
      (pullback.fst _ _) := isGrpPullback_pullback A₀ (spMap (algebraMap k R))
  have hf : pullback.lift φ (A.hom ≫ spMap R.val.toRingHom) w ≫ pullback.fst _ _ = φ := pullback.lift_fst _ _ _
  refine ⟨inst, pullback.lift φ (A.hom ≫ spMap R.val.toRingHom) w, h₁, ?_, hf⟩
  exact IsGrpPullback.cancel h₁ (h.congr es.symm hf.symm) (pullback.lift_snd _ _ _)

end GlobalTheory.CompanionTheory.Ar.Approx
