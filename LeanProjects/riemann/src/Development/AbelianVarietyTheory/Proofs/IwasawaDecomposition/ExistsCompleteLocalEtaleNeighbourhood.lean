import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsCoverModels
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan

theorem essFiniteType_int_stalk (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (s : X ⟶ Sp F)
    [LocallyOfFiniteType s] (x : X) : Algebra.EssFiniteType ℤ (X.presheaf.stalk x) := by
  have h1 : (s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap s x
  let p : PrimeSpectrum F := s x
  have h2 : (algebraMap F ((Spec.structureSheaf F).presheaf.stalk p)).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl)
  have hQ : Algebra.EssFiniteType ℤ ℚ := Algebra.EssFiniteType.of_isLocalization ℚ (nonZeroDivisors ℤ)
  have hF : Algebra.EssFiniteType ℚ F := inferInstance
  have hZF : Algebra.EssFiniteType ℤ F := Algebra.EssFiniteType.comp ℤ ℚ F
  have h3 : (algebraMap ℤ F).EssFiniteType := RingHom.essFiniteType_algebraMap.2 hZF
  have h4 := (h3.comp h2).comp h1
  rw [← RingHom.essFiniteType_algebraMap]
  convert h4
  exact RingHom.ext_int _ _

theorem exists_ringHom_stalk (F : Type) [Field F] (X : Scheme.{0}) (s : X ⟶ Sp F) (x : X) :
    Nonempty (F →+* X.presheaf.stalk x) := by
  let p : PrimeSpectrum F := s x
  exact ⟨(s.stalkMap x).hom.comp (algebraMap F ((Spec.structureSheaf F).presheaf.stalk p))⟩

theorem stalk_factor_eq {X : Scheme.{0}} {R : CommRingCat.{0}} {x y : X} (hy : y = x) (φ : X.presheaf.stalk x ⟶ R)
    (ψ : X.presheaf.stalk y ⟶ R) (h : Spec.map ψ ≫ X.fromSpecStalk y = Spec.map φ ≫ X.fromSpecStalk x) :
    ∃ e : X.presheaf.stalk y →+* X.presheaf.stalk x, Function.Bijective e ∧ ψ.hom = φ.hom.comp e := by
  subst hy
  refine ⟨RingHom.id _, Function.bijective_id, ?_⟩
  have : ψ = φ := Spec.map_injective ((cancel_mono _).1 h)
  subst this
  rfl

end GlobalTheory.GenFan

namespace GlobalTheory.GenFan

theorem exists_chart : ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (s : X ⟶ Sp F), LocallyOfFiniteType s →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ x : X, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R)
    (ξ : Sp R ⟶ X), IsCN R ∧ ξ (closedPoint R) = x ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
    ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified ∧ ∀ p, ξ p ⤳ x := by
  intro F _ _ X s hs hN x
  obtain ⟨hd, hic⟩ := hN x
  haveI : IsDomain (X.presheaf.stalk x) := hd
  haveI : IsIntegrallyClosed (X.presheaf.stalk x) := hic
  haveI : Algebra.EssFiniteType ℤ (X.presheaf.stalk x) := essFiniteType_int_stalk F X s x
  haveI : IsNoetherianRing (X.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  obtain ⟨ι⟩ := exists_ringHom_stalk F X s x
  haveI : CharZero (X.presheaf.stalk x) := (RingHom.charZero_iff ι.injective).1 inferInstance
  have fg : (maximalIdeal (X.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :=
    AdicCompletion.isLocalRing_of_fg fg
  obtain ⟨hRd, hRi⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (X.presheaf.stalk x)
  haveI hRn : IsNoetherianRing (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  set R := AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) with hR
  set φ := algebraMap (X.presheaf.stalk x) R with hφ
  haveI : IsLocalHom φ := ((IsLocalRing.local_hom_TFAE φ).out 0 2).mpr hm.symm.le
  have hres : Function.Surjective ((residue R).comp φ) := by
    intro r
    obtain ⟨a, ha⟩ := (AdicCompletion.residueField_map_bijective (X.presheaf.stalk x)).2 r
    obtain ⟨b, rfl⟩ := residue_surjective a
    refine ⟨b, ?_⟩
    rw [← ha, RingHom.comp_apply, ResidueField.map_residue]
  let ξ : Sp R ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x
  have hξ : ∀ p, ξ p = X.fromSpecStalk x (Spec.map (CommRingCat.ofHom φ) p) := fun p => Scheme.Hom.comp_apply _ _ _
  have hx : ξ (closedPoint R) = x := by
    refine (hξ _).trans ?_
    have : Spec.map (CommRingCat.ofHom φ) (closedPoint R) = closedPoint (X.presheaf.stalk x) := comap_closedPoint φ
    rw [this]
    exact Scheme.fromSpecStalk_closedPoint
  obtain ⟨e, he, hψ⟩ := stalk_factor_eq hx (CommRingCat.ofHom φ) (Scheme.stalkClosedPointTo ξ)
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)
  refine ⟨R, inferInstance, hRd, hloc, ξ, ⟨hRn, hRi, ?_, ?_⟩, hx, ?_, ?_, ?_⟩
  · rw [hm]
    exact AdicCompletion.isAdicComplete_self _ fg
  · exact (RingHom.charZero_iff (φ.comp ι).injective).1 inferInstance
  · rw [hψ]
    exact isEtaleCompletion_comp_bij e he φ ⟨RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _),
      hm.symm, RingHom.Finite.of_surjective _ hres⟩
  · rw [hψ, ← RingHom.comp_assoc]
    exact RingHom.FormallyUnramified.of_surjective (hres.comp he.2)
  · intro p
    have h : ξ p ∈ Set.range (X.fromSpecStalk x) := ⟨_, (hξ p).symm⟩
    rwa [Scheme.range_fromSpecStalk] at h

end GlobalTheory.GenFan
