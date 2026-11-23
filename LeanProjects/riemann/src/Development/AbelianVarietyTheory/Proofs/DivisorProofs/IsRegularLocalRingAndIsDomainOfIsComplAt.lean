import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem isRegularLocalRing_and_isDomain_of_isComplAt :
    ∀ (W : Type) [CommRing W] [IsRegularLocalRing W] (I : Type) [Fintype I] (R : Type) [CommRing R]
      [IsLocalRing R] (ψ : MvPolynomial I W →+* R), IsComplAt ψ → IsLocalHom (ψ.comp MvPolynomial.C) →
      IsRegularLocalRing R ∧ IsDomain R := by
  intro W _ _ I _ R _ _ ψ hψ _
  obtain ⟨hnoeth, -, hflat, hmap, -⟩ := hψ
  haveI : IsRegularRing W := GlobalTheory.isRegularRing_of_isRegularLocalRing W
  set q : Ideal (MvPolynomial I W) := (maximalIdeal R).comap ψ with hq
  haveI : q.IsPrime := Ideal.comap_isPrime ψ (maximalIdeal R)
  let L := Localization.AtPrime q
  haveI : IsRegularLocalRing L := IsRegularRing.isRegularLocalRing_localization q
  have hu : ∀ y : q.primeCompl, IsUnit (ψ y) := by
    intro y
    by_contra h
    exact y.2 ((mem_maximalIdeal _).2 h)
  let φ : L →+* R := IsLocalization.lift (M := q.primeCompl) hu
  letI : Algebra (MvPolynomial I W) R := ψ.toAlgebra
  letI : Algebra L R := φ.toAlgebra
  haveI : IsScalarTower (MvPolynomial I W) L R := IsScalarTower.of_algebraMap_eq (fun a => by
    change ψ a = φ (algebraMap _ L a)
    exact (IsLocalization.lift_eq (M := q.primeCompl) hu a).symm)
  haveI : Module.Flat (MvPolynomial I W) R := hflat
  haveI : IsLocalizedModule q.primeCompl (LinearMap.id : R →ₗ[MvPolynomial I W] R) :=
    isLocalizedModule_id q.primeCompl R L
  haveI : Module.Flat L R :=
    Module.Flat.of_isLocalizedModule L q.primeCompl (LinearMap.id : R →ₗ[MvPolynomial I W] R)
  haveI : IsNoetherianRing R := hnoeth
  have hm : maximalIdeal R = (maximalIdeal L).map (algebraMap L R) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact hmap.symm
  haveI hreg : IsRegularLocalRing R :=
    GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal L R (maximalIdeal L) hm
  exact ⟨hreg, (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).1⟩

end GlobalTheory.TChart
