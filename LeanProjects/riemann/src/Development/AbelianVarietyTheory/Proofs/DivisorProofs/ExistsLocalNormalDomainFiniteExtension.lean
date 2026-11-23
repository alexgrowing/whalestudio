import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

open scoped Pointwise

namespace GlobalTheory.LocalNormalExt

theorem exists_eq_of_mul_mem_integralClosure
    (R K K' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    [Field K'] [Algebra K K'] [FiniteDimensional K K'] [Algebra R K'] [IsScalarTower R K K']
    (P : Ideal (integralClosure R K')) [P.IsMaximal]
    (x : K) (s : integralClosure R K') (hs : s ∉ P)
    (hx : algebraMap K K' x * (s : K') ∈ integralClosure R K') :
    ∃ r : R, algebraMap R K r = x := by
  classical
  let L := IntermediateField.normalClosure K K' (AlgebraicClosure K')
  letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R K' L := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply R K K', ← IsScalarTower.algebraMap_apply K K' L]; rfl)
  haveI : FiniteDimensional K L := inferInstance
  haveI : IsGalois K L := inferInstance
  haveI : IsScalarTower R R L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let S := integralClosure R L
  let C := integralClosure R K'
  haveI : IsFractionRing S L := integralClosure.isFractionRing_of_finite_extension K L
  let f : C →ₐ[R] S := ((IsScalarTower.toAlgHom R K' L).comp C.val).codRestrict S
    (fun c => (c.2 : IsIntegral R (c : K')).map (IsScalarTower.toAlgHom R K' L))
  have hfv : ∀ c : C, ((f c : S) : L) = algebraMap K' L (c : K') := fun _ => rfl
  have hfinj : Function.Injective f := by
    intro c d h
    have := congrArg (fun u : S => (u : L)) h
    simp only [hfv] at this
    exact Subtype.ext ((algebraMap K' L).injective this)
  letI : Algebra C S := f.toRingHom.toAlgebra
  haveI : IsScalarTower R C S := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  haveI : Algebra.IsIntegral C S := ⟨fun u => (Algebra.IsIntegral.isIntegral (R := R) u).tower_top⟩
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S) P
    (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap C S)).mp hfinj]; exact bot_le)
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  let J : Ideal S :=
    { carrier := {u | ∃ v : S, u * algebraMap R S a = algebraMap R S b * v}
      add_mem' := by
        rintro u₁ u₂ ⟨v₁, h₁⟩ ⟨v₂, h₂⟩
        exact ⟨v₁ + v₂, by rw [add_mul, h₁, h₂, mul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c u ⟨v, h⟩
        exact ⟨c * v, by rw [smul_eq_mul, _root_.mul_assoc, h, mul_left_comm]⟩ }
  have hJg : ∀ (g : S ≃ₐ[R] S) (u : S), u ∈ J → g u ∈ J := by
    rintro g u ⟨v, h⟩
    exact ⟨g v, by rw [← g.commutes a, ← g.commutes b, ← map_mul, h, map_mul]⟩

  have e1 : ∀ r : R, ((algebraMap R S r : S) : L) = algebraMap K L (algebraMap R K r) :=
    fun _ => rfl
  have hbL : algebraMap K L (algebraMap R K b) ≠ 0 := (map_ne_zero _).mpr hb0
  have htJ : f s ∈ J := by
    refine ⟨f ⟨_, hx⟩, ?_⟩
    apply Subtype.ext
    show (f s : L) * ((algebraMap R S a : S) : L) = ((algebraMap R S b : S) : L) * (f ⟨_, hx⟩ : L)
    rw [hfv, hfv, e1, e1]
    simp only [map_mul]
    rw [← IsScalarTower.algebraMap_apply K K' L, ← hab, map_div₀]
    field_simp
  have hmax : ∀ (I : Ideal S) [I.IsMaximal], I.under R = IsLocalRing.maximalIdeal R :=
    fun I _ => IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal I)
  have hJtop : J = ⊤ := by
    by_contra hne
    obtain ⟨N, hNmax, hJN⟩ := Ideal.exists_le_maximal J hne
    haveI : Finite (S ≃ₐ[R] S) := Finite.of_equiv _ (galRestrict R K L S).toEquiv
    haveI : Algebra.IsInvariant R S (S ≃ₐ[R] S) := Algebra.isInvariant_of_isGalois' R K L S
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (A := R) (B := S) (G := S ≃ₐ[R] S) Q N
      ((hmax Q).trans (hmax N).symm)
    have h1 : g • f s ∈ g • Q := by
      rw [← hg]; exact hJN (hJg g _ htJ)
    have h2 : f s ∈ Q := (Ideal.smul_mem_pointwise_smul_iff).mp h1
    exact hs (by rw [← hQ]; exact h2)
  obtain ⟨v, hv⟩ : (1 : S) ∈ J := hJtop ▸ Submodule.mem_top
  have hvL : (v : L) = algebraMap K L x := by
    have := congrArg (fun u : S => (u : L)) hv
    simp only [_root_.one_mul, Subalgebra.coe_mul, e1] at this
    rw [← hab, map_div₀, this]
    field_simp
  have hint : IsIntegral R (algebraMap K L x) := hvL ▸ v.2
  have hxint : IsIntegral R x :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L) (algebraMap K L).injective).mp hint
  exact IsIntegrallyClosed.isIntegral_iff.mp hxint

theorem exists_local_normal_domain_of_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (K' : Type) [Field K'] [Algebra (FractionRing R) K'] [FiniteDimensional (FractionRing R) K'], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (_ : IsNoetherianRing R') (_ : IsIntegrallyClosed R') (ρ : R →+* R') (e : FractionRing R' ≃+* K'), IsLocalHom ρ ∧ Function.Injective ρ ∧ (∀ r, e (algebraMap R' _ (ρ r)) = algebraMap (FractionRing R) K' (algebraMap R _ r)) ∧ ∀ (x : FractionRing R) (w : R'), e (algebraMap R' _ w) = algebraMap (FractionRing R) K' x → ∃ r : R, algebraMap R _ r = x := by
  intro R _ _ _ _ _ _ K' _ _ _
  classical
  let K := FractionRing R
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  letI : Algebra R K' := ((algebraMap K K').comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let C := integralClosure R K'
  haveI : IsFractionRing C K' := integralClosure.isFractionRing_of_finite_extension K K'
  haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K
  haveI : IsNoetherianRing C := IsIntegralClosure.isNoetherianRing R K K' C
  haveI : IsDomain C := inferInstance
  obtain ⟨m', hm'⟩ := Ideal.exists_maximal C
  obtain ⟨R', _, _, _⟩ : ∃ (R' : Type) (_ : CommRing R') (_ : Algebra C R'),
      IsLocalization.AtPrime R' m' :=
    ⟨Localization.AtPrime m', inferInstance, inferInstance, inferInstance⟩
  haveI : IsLocalRing R' := IsLocalization.AtPrime.isLocalRing R' m'
  haveI : IsDomain R' :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := m'.primeCompl) (S := R') m'.primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing R' := IsLocalization.isNoetherianRing m'.primeCompl R' inferInstance
  haveI : IsIntegrallyClosed R' :=
    isIntegrallyClosed_of_isLocalization R' m'.primeCompl m'.primeCompl_le_nonZeroDivisors
  letI : Algebra R' K' := (IsLocalization.lift (M := m'.primeCompl) (S := R') (g := algebraMap C K')
    (fun y => IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective C K')).mpr
      (fun h => y.2 (h ▸ m'.zero_mem))))).toAlgebra
  haveI : IsScalarTower C R' K' :=
    IsScalarTower.of_algebraMap_eq (fun c => (IsLocalization.lift_eq _ c).symm)
  haveI : IsFractionRing R' K' :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m'.primeCompl R' K'
  let e : FractionRing R' ≃+* K' :=
    (FractionRing.algEquiv R' K').toRingEquiv
  have he : ∀ w : R', e (algebraMap R' _ w) = algebraMap R' K' w := fun w =>
    (FractionRing.algEquiv R' K').commutes w
  have hRC : ∀ r : R, algebraMap C K' (algebraMap R C r) = algebraMap K K' (algebraMap R K r) :=
    fun _ => rfl
  have hinjRC : Function.Injective (algebraMap R C) := by
    intro a b h
    have := congrArg (algebraMap C K') h
    rw [hRC, hRC] at this
    exact IsFractionRing.injective R K ((algebraMap K K').injective this)
  have hinjCR' : Function.Injective (algebraMap C R') :=
    IsLocalization.injective R' m'.primeCompl_le_nonZeroDivisors
  have hcomap : m'.comap (algebraMap R C) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m')
  refine ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (algebraMap C R').comp (algebraMap R C), e, ?_, hinjCR'.comp hinjRC, ?_, ?_⟩
  · refine ⟨fun r hr => ?_⟩
    by_contra hnu
    have h1 : algebraMap R C r ∈ m' := by
      rw [← Ideal.mem_comap, hcomap]; exact hnu
    have h2 : algebraMap C R' (algebraMap R C r) ∈ IsLocalRing.maximalIdeal R' := by
      rw [IsLocalization.AtPrime.to_map_mem_maximal_iff R' m']; exact h1
    exact (IsLocalRing.mem_maximalIdeal _).mp h2 hr
  · intro r
    rw [he]
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply C R' K', hRC]
  · intro x w hw
    rw [he] at hw
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective m'.primeCompl w
    have hmul : algebraMap K K' x * (s : C) = (c : K') := by
      rw [← hw]
      have := congrArg (algebraMap R' K') (IsLocalization.mk'_spec R' c s)
      rw [map_mul, ← IsScalarTower.algebraMap_apply C R' K', ← IsScalarTower.algebraMap_apply C R' K'] at this
      exact this
    exact exists_eq_of_mul_mem_integralClosure R K K' m' x (s : C) s.2 (hmul ▸ c.2)

end GlobalTheory.LocalNormalExt
