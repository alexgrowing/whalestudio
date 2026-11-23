import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedOfGenericFiberSmoothProperStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem geometricallyConnected_snd_snd_iff {X S S' S'' : Scheme.{0}} (g : X ⟶ S) (f : S' ⟶ S)
    (b : S'' ⟶ S') :
    GeometricallyConnected (pullback.snd (pullback.snd g f) b) ↔
      GeometricallyConnected (pullback.snd g (b ≫ f)) := by
  haveI : MorphismProperty.RespectsIso @GeometricallyConnected :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [← pullbackLeftPullbackSndIso_hom_snd g f b]
  exact MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected _ _

private theorem spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) : spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem stableUnderSpecialization_geometricallyConnected :
    ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G],
      Smooth G.hom → IsProper G.hom →
      StableUnderSpecialization {x : PrimeSpectrum k | GeometricallyConnected
        (pullback.snd G.hom (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  intro k _ _ G _ _ hsm hpr x y hxy hx
  haveI := hsm
  haveI := hpr
  have hle : x.asIdeal ≤ y.asIdeal := (PrimeSpectrum.le_iff_specializes x y).mpr hxy
  have hs' : Smooth ((Over.pullback (spMap (algebraMap k (k ⧸ x.asIdeal)))).obj G).hom := by
    show Smooth (pullback.snd G.hom (spMap (algebraMap k (k ⧸ x.asIdeal))))
    infer_instance
  have hp' : IsProper ((Over.pullback (spMap (algebraMap k (k ⧸ x.asIdeal)))).obj G).hom := by
    show IsProper (pullback.snd G.hom (spMap (algebraMap k (k ⧸ x.asIdeal))))
    infer_instance
  have hgen : GeometricallyConnected (pullback.snd
      ((Over.pullback (spMap (algebraMap k (k ⧸ x.asIdeal)))).obj G).hom
      (spMap (algebraMap (k ⧸ x.asIdeal) x.asIdeal.ResidueField))) := by
    show GeometricallyConnected (pullback.snd (pullback.snd G.hom (spMap (algebraMap k (k ⧸ x.asIdeal))))
      (spMap (algebraMap (k ⧸ x.asIdeal) x.asIdeal.ResidueField)))
    rw [geometricallyConnected_snd_snd_iff, spMap_comp_moduli_spaces, ← IsScalarTower.algebraMap_eq]
    exact hx
  have hG' : GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k (k ⧸ x.asIdeal)))) :=
    GlobalTheory.T.geometricallyConnected_of_generic_fiber_smooth_proper (k ⧸ x.asIdeal) x.asIdeal.ResidueField
      ((Over.pullback (spMap (algebraMap k (k ⧸ x.asIdeal)))).obj G) hs' hp' hgen
  have hker : ∀ a ∈ x.asIdeal, algebraMap k y.asIdeal.ResidueField a = 0 := fun a ha =>
    Ideal.algebraMap_residueField_eq_zero.mpr (hle ha)
  have hφ : (Ideal.Quotient.lift x.asIdeal (algebraMap k y.asIdeal.ResidueField) hker).comp
      (algebraMap k (k ⧸ x.asIdeal)) = algebraMap k y.asIdeal.ResidueField := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.lift_comp_mk _ _ _
  show GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k y.asIdeal.ResidueField)))
  rw [← hφ, ← spMap_comp_moduli_spaces, ← geometricallyConnected_snd_snd_iff]
  infer_instance

end GlobalTheory.CompanionTheory.Ar.Approx
