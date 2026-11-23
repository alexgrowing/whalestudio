import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplicationImpor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.Desc

theorem surjective_U_hom {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} (hπ : Surjective π)
    {G' : Over S} [GrpObj G'] (N : Near π G') : Surjective N.U.hom := by
  have := N.smooth
  obtain ⟨s, hs⟩ := π.surjective (closedPoint R)
  let e : S ⟶ G'.left := (1 : Over.mk (𝟙 S) ⟶ G').left
  have he : e ≫ G'.hom = 𝟙 S := Over.w (1 : Over.mk (𝟙 S) ⟶ G')
  have hes : G'.hom (e s) = s := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  obtain ⟨z, hz⟩ : e s ∈ Set.range N.u := N.all _ (by rw [hes]; exact hs)
  have hzs : pullback.snd N.U.hom π z = s := by
    rw [← N.u_over, Scheme.Hom.comp_apply, hz, hes]
  have hc : closedPoint R ∈ Set.range N.U.hom := ⟨pullback.fst N.U.hom π z, by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hzs, hs]⟩
  exact ⟨fun x => (Flat.generalizingMap N.U.hom).stableUnderGeneralization_range
    (IsLocalRing.specializes_closedPoint x) hc⟩

theorem surjective_UT_hom : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), Surjective π →
    ∀ (G' : Over S) [GrpObj G'] (N : Near π G'), Surjective (Desc.UT N).hom := by
  intro R _ _ S π hπ G' _ N
  have := surjective_U_hom hπ N
  exact inferInstanceAs (Surjective (pullback.snd N.U.hom (pullback.fst π π ≫ π)))

end GlobalTheory.Mum.Desc
