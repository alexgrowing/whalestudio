import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundleIsoDescendsToSubringOfFinset
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MorphismDescendsToSubring
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsNoethModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory

theorem sections_eq_of_spMap_subtype_comp_eq : ∀ (R : Type) [CommRing R] (R₀ : Subring R) (X : Scheme.{0})
    (p : X ⟶ Sp R₀) [IsSeparated p] (x y : Sp R₀ ⟶ X), x ≫ p = y ≫ p →
    spMap R₀.subtype ≫ x = spMap R₀.subtype ≫ y → x = y := by
  intro R _ R₀ X p _ x y hp hR
  let l : Sp R₀ ⟶ pullback p p := pullback.lift x y hp
  let c : pullback (pullback.diagonal p) l ⟶ Sp R₀ := pullback.snd _ _
  haveI : IsClosedImmersion c := inferInstance
  have e1 : l ≫ pullback.fst p p = x := pullback.lift_fst _ _ _
  have e2 : l ≫ pullback.snd p p = y := pullback.lift_snd _ _ _
  have hc : c ≫ x = c ≫ y := by
    have h1 : c ≫ l ≫ pullback.fst p p = c ≫ l ≫ pullback.snd p p := by
      rw [← Category.assoc c l, ← Category.assoc c l]
      change (pullback.snd (pullback.diagonal p) l ≫ l) ≫ _ = (pullback.snd (pullback.diagonal p) l ≫ l) ≫ _
      rw [← pullback.condition, Category.assoc, Category.assoc,
        pullback.diagonal_fst, pullback.diagonal_snd]
    rwa [e1, e2] at h1
  let k : Sp R ⟶ pullback (pullback.diagonal p) l :=
    pullback.lift (spMap R₀.subtype ≫ x) (spMap R₀.subtype) (by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id, Category.assoc, e1]
      · rw [Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id, Category.assoc, e2, hR])
  have hk : k ≫ c = spMap R₀.subtype := pullback.lift_snd _ _ _
  obtain ⟨hZ, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine c
  have hinj0 : Function.Injective (spMap R₀.subtype).appTop := by
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom R₀.subtype)
    have : (spMap R₀.subtype).appTop = (Scheme.ΓSpecIso (CommRingCat.of R₀)).hom ≫
        CommRingCat.ofHom R₀.subtype ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv := by
      rw [← Category.assoc, ← e]; simp
    rw [this]
    intro a b hab
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hab
    have := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective hab
    exact (Scheme.ΓSpecIso (CommRingCat.of R₀)).commRingCatIsoToRingEquiv.injective (Subtype.val_injective this)
  have hinj : Function.Injective c.appTop := by
    rw [← hk, Scheme.Hom.comp_appTop] at hinj0
    simp only [CommRingCat.hom_comp, RingHom.coe_comp] at hinj0
    exact hinj0.of_comp
  haveI : IsIso c.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  haveI : IsIso c :=
    (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _) (arrowIsoSpecΓOfIsAffine c)).mpr
      (inferInstanceAs (IsIso (Spec.map c.appTop)))
  rw [← cancel_epi c]
  exact hc

end GlobalTheory
