import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsHasProjectiveDimensionLEOfResidueField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsPrincipalMapAwayOfHasProjectiveDimensionLE
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericFibreFactorial

theorem isRegularRing_localization_of_comap_eq_bot (R A : Type) [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A] (p : Ideal A) [p.IsPrime]
    (hp : p.comap (algebraMap R A) = ⊥) : IsRegularRing (Localization.AtPrime p) := by
  let K := FractionRing R
  let M := Algebra.algebraMapSubmonoid A (nonZeroDivisors R)
  let B := Localization M
  letI : Algebra K B := localizationAlgebra (nonZeroDivisors R) A
  haveI : IsScalarTower R K B := inferInstance
  haveI h1 : Algebra.IsPushout R A K B :=
    Algebra.isPushout_of_isLocalization (nonZeroDivisors R) K A B
  haveI : Algebra.IsPushout R K A B := h1.symm
  haveI : Algebra.Smooth K B := Algebra.Smooth.of_equiv (Algebra.IsPushout.equiv (R := R) (S := K) (R' := A) (S' := B))
  haveI : IsRegularRing B := GlobalTheory.isRegularRing_of_smooth K B
  have disj : Disjoint (M : Set A) (p : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrp
    have : r ∈ p.comap (algebraMap R A) := hrp
    rw [hp, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hr this
  let q := p.map (algebraMap A B)
  haveI : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M B p inferInstance disj
  haveI : IsLocalization.AtPrime (Localization.AtPrime q) p := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime q) q
    exact (IsLocalization.under_map_of_isPrime_disjoint M B inferInstance disj).symm
  haveI : IsRegularRing (Localization.AtPrime q) :=
    GlobalTheory.ExtendRig.isRegularRing_of_isLocalization q.primeCompl _
  exact IsRegularRing.of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime q) (Localization.AtPrime p)).toRingEquiv

theorem ufd_stalk_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Sp R) [Smooth f] (x : X), (show PrimeSpectrum R from f x).asIdeal = ⊥ →
    UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  intro R _ _ X _ f _ x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hs : (f.appLE ⊤ U le_top).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  haveI : Nonempty (⊤ : (Sp R).Opens) := ⟨⟨f x, trivial⟩⟩
  haveI : IsDomain Γ(Sp R, ⊤) := inferInstance
  have hgen : f x = genericPoint (Sp R) := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hx
  have h1 := IsAffineOpen.comap_primeIdealOf_appLE (f := f) ⊤ (isAffineOpen_top _) U hU le_top hxU
  have h2 : (isAffineOpen_top (Sp R)).primeIdealOf ⟨f x, (show f x ∈ (⊤ : (Sp R).Opens) from trivial)⟩ =
      genericPoint (Spec Γ(Sp R, ⊤)) := by
    rw [← (isAffineOpen_top (Sp R)).primeIdealOf_genericPoint]
    congr 1
    exact Subtype.ext hgen
  rw [h2, genericPoint_eq_bot_of_affine] at h1
  have hcomap : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.comap (f.appLE ⊤ U le_top).hom = ⊥ :=
    congrArg PrimeSpectrum.asIdeal h1
  algebraize [(f.appLE ⊤ U le_top).hom]
  have hreg := isRegularRing_localization_of_comap_eq_bot Γ(Sp R, ⊤) Γ(X, U)
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal hcomap
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  haveI : IsRegularRing (X.presheaf.stalk x) :=
    IsRegularRing.of_ringEquiv (IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (Localization.AtPrime (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) (X.presheaf.stalk x)).toRingEquiv
  exact GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
    GlobalTheory.exists_hasProjectiveDimensionLE_of_isRegularLocalRing
    GlobalTheory.isPrincipal_map_away_of_hasProjectiveDimensionLE _

end GlobalTheory.GenericFibreFactorial
