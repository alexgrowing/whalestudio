import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThValAtAndNotIsThValue
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbGenericFibre

theorem baseChange_normal_generic : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (χ : Sp R ⟶ S), IsLocallyNoetherian (Over.mk χ ⊗ G).left ∧ GlobalTheory.IsNormalScheme (Over.mk χ ⊗ G).left ∧ IsPreimmersion ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ∧ ∀ W : (Over.mk χ ⊗ G).left.Opens, Function.Injective ((((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left.app W).hom) := by
  intro S G _ hG R _ _ _ _ χ
  set K := FractionRing R
  set T : Over S := Over.mk χ
  set TK : Over S := Over.mk (spMap (algebraMap R K) ≫ χ)
  set h : TK ⟶ T := Over.homMk (spMap (algebraMap R K)) rfl
  have hpb : IsPullback (h ▷ G).left (CartesianMonoidalCategory.fst TK G).left
      (CartesianMonoidalCategory.fst T G).left (spMap (algebraMap R K)) :=
    GlobalTheory.ThetaRuleCompare.isPullback_whisker h
  have hsm : Smooth G.hom := hG.smooth
  have h1 : IsPullback (CartesianMonoidalCategory.snd T G).left (CartesianMonoidalCategory.fst T G).left G.hom T.hom :=
    (IsPullback.of_hasPullback T.hom G.hom).flip
  have hsf : Smooth (CartesianMonoidalCategory.fst T G).left := MorphismProperty.of_isPullback h1 hsm
  have : IsLocallyNoetherian T.left := (inferInstance : IsLocallyNoetherian (Sp R))
  have : IsLocallyNoetherian (T ⊗ G).left := LocallyOfFiniteType.isLocallyNoetherian (CartesianMonoidalCategory.fst T G).left
  have : GlobalTheory.IsNormalScheme T.left := (inferInstance : GlobalTheory.IsNormalScheme (Sp R))
  have : IsPreimmersion (spMap (algebraMap R K)) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  refine ⟨inferInstance, GlobalTheory.isNormalScheme_of_smooth (CartesianMonoidalCategory.fst T G).left,
    MorphismProperty.of_isPullback hpb.flip ‹_›, fun W => ?_⟩
  exact GlobalTheory.Exist.CubicalExtension.app_injective_generic hpb W

end GlobalTheory.SemiAbGenericFibre
