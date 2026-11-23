import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSurjectiveOfIsCplAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem isRegularLocalRing_of_flat_of_map_comap_maximalIdeal (V : Type) [CommRing V]
    [IsRegularLocalRing V] (I : Type) [Fintype I] (S : Type) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (φ : MvPolynomial I V →+* S) (hflat : φ.Flat)
    (hmap : ((maximalIdeal S).comap φ).map φ = maximalIdeal S) : IsRegularLocalRing S := by
  haveI : IsRegularRing V := GlobalTheory.isRegularRing_of_isRegularLocalRing V
  set q : Ideal (MvPolynomial I V) := (maximalIdeal S).comap φ with hq
  haveI : q.IsPrime := Ideal.comap_isPrime φ (maximalIdeal S)
  let L := Localization.AtPrime q
  haveI : IsRegularLocalRing L := IsRegularRing.isRegularLocalRing_localization q
  have hu : ∀ y : q.primeCompl, IsUnit (φ y) := by
    intro y
    by_contra h
    exact y.2 ((mem_maximalIdeal _).2 h)
  let χ : L →+* S := IsLocalization.lift (M := q.primeCompl) hu
  letI : Algebra (MvPolynomial I V) S := φ.toAlgebra
  letI : Algebra L S := χ.toAlgebra
  haveI : IsScalarTower (MvPolynomial I V) L S := IsScalarTower.of_algebraMap_eq (fun a => by
    change φ a = χ (algebraMap _ L a)
    exact (IsLocalization.lift_eq (M := q.primeCompl) hu a).symm)
  haveI : Module.Flat (MvPolynomial I V) S := hflat
  haveI : IsLocalizedModule q.primeCompl (LinearMap.id : S →ₗ[MvPolynomial I V] S) :=
    isLocalizedModule_id q.primeCompl S L
  haveI : Module.Flat L S :=
    Module.Flat.of_isLocalizedModule L q.primeCompl (LinearMap.id : S →ₗ[MvPolynomial I V] S)
  have hm : maximalIdeal S = (maximalIdeal L).map (algebraMap L S) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact hmap.symm
  exact GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal L S (maximalIdeal L) hm

theorem isRegularLocalRing_quotient_of_isComplAt :
    ∀ (W : Type) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] (I : Type) [Fintype I] (R : Type) [CommRing R]
      [IsLocalRing R] (ψ : MvPolynomial I W →+* R), IsComplAt ψ → IsLocalHom (ψ.comp MvPolynomial.C) →
      ∀ 𝔭 : Ideal W, 𝔭 ≠ ⊤ → IsRegularLocalRing (W ⧸ 𝔭) →
        IsRegularLocalRing (R ⧸ 𝔭.map (ψ.comp MvPolynomial.C)) := by
  intro W _ _ _ I _ R _ _ ψ hψ hloc 𝔭 h𝔭 hreg
  obtain ⟨hnoeth, -, hflat, hmap, -⟩ := hψ
  haveI : IsNoetherianRing R := hnoeth
  haveI : IsRegularLocalRing (W ⧸ 𝔭) := hreg
  rw [← Ideal.map_map]
  set J : Ideal R := (Ideal.map MvPolynomial.C 𝔭).map ψ with hJ
  have hJm : J ≤ maximalIdeal R := by
    rw [hJ, Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact h𝔭 (Ideal.eq_top_of_isUnit_mem _ hx (isUnit_of_map_unit _ _ hu))
  haveI : Nontrivial (R ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJm)
  haveI : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let e := MvPolynomial.quotientEquivQuotientMvPolynomial (σ := I) 𝔭
  have heC : ∀ a : W, e (MvPolynomial.C (Ideal.Quotient.mk 𝔭 a)) = Ideal.Quotient.mk _ (MvPolynomial.C a) := by
    intro a; simp [e, MvPolynomial.quotientEquivQuotientMvPolynomial]
  have heX : ∀ i : I, e (MvPolynomial.X i) = Ideal.Quotient.mk _ (MvPolynomial.X i) := by
    intro i; simp [e, MvPolynomial.quotientEquivQuotientMvPolynomial]
  let ψ' : MvPolynomial I (W ⧸ 𝔭) →+* R ⧸ J :=
    (Ideal.quotientMap J ψ Ideal.le_comap_map).comp e.toRingEquiv.toRingHom
  have hflat' : ψ'.Flat :=
    (RingHom.Flat.of_bijective e.bijective).comp (GlobalTheory.Pat.flat_quotientMap_map ψ hflat _)
  let π : MvPolynomial I W →+* MvPolynomial I (W ⧸ 𝔭) := MvPolynomial.map (Ideal.Quotient.mk 𝔭)
  have hcomm : ψ'.comp π = (Ideal.Quotient.mk J).comp ψ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, π, MvPolynomial.map_C, ψ']
      change Ideal.quotientMap J ψ Ideal.le_comap_map (e (MvPolynomial.C (Ideal.Quotient.mk 𝔭 a))) = _
      rw [heC, Ideal.quotientMap_mk]
    · intro i
      simp only [RingHom.comp_apply, π, MvPolynomial.map_X, ψ']
      change Ideal.quotientMap J ψ Ideal.le_comap_map (e (MvPolynomial.X i)) = _
      rw [heX, Ideal.quotientMap_mk]
  have hmax : maximalIdeal (R ⧸ J) = (maximalIdeal R).map (Ideal.Quotient.mk J) := by
    exact (IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
  refine isRegularLocalRing_of_flat_of_map_comap_maximalIdeal (W ⧸ 𝔭) I (R ⧸ J) ψ' hflat' ?_
  refine le_antisymm Ideal.map_comap_le ?_
  have h1 : maximalIdeal (R ⧸ J) = (((maximalIdeal R).comap ψ).map π).map ψ' := by
    rw [hmax, Ideal.map_map, hcomm, ← Ideal.map_map, hmap]
  refine h1.le.trans (Ideal.map_mono ?_)
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, hcomm, ← Ideal.comap_comap]
  apply Ideal.comap_mono
  rw [hmax]
  exact Ideal.le_comap_map

end GlobalTheory.TChart
