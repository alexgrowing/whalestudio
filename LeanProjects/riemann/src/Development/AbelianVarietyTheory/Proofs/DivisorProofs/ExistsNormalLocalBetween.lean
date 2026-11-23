import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeOfMonic
open IsLocalRing Polynomial

noncomputable section
namespace GlobalTheory.LocAcycEmbed

theorem exists_eq_of_aeval_eq_zero {T K : Type} [CommRing T] [IsDomain T] [Field K] [Algebra T K]
    (hT : GlobalTheory.LocAcyc.AbsIntClosed T) :
    ∀ (n : ℕ) (f : T[X]), f.Monic → f.natDegree = n → ∀ x : K, aeval x f = 0 →
      ∃ t : T, algebraMap T K t = x := by
  intro n
  induction n with
  | zero =>
    intro f hf hn x hx
    have h1 : f = 1 := Polynomial.eq_one_of_monic_natDegree_zero hf hn
    subst h1
    simp at hx
  | succ n ih =>
    intro f hf hn x hx
    obtain ⟨r, hr⟩ := hT f hf (by omega)
    have hfg : (X - C r) * (f /ₘ (X - C r)) = f := mul_divByMonic_eq_iff_isRoot.2 hr
    have hg : (f /ₘ (X - C r)).Monic := by
      apply Polynomial.Monic.of_mul_monic_left (monic_X_sub_C r)
      rw [hfg]; exact hf
    have hgn : (f /ₘ (X - C r)).natDegree = n := by
      have := Polynomial.Monic.natDegree_mul (monic_X_sub_C r) hg
      rw [hfg, natDegree_X_sub_C] at this
      omega
    rw [← hfg, map_mul] at hx
    rcases mul_eq_zero.1 hx with h | h
    · refine ⟨r, ?_⟩
      simp at h
      rw [sub_eq_zero] at h
      exact h.symm
    · exact ih _ hg hgn x h

theorem isIntegrallyClosed_of_absIntClosed (T : Type) [CommRing T] [IsDomain T]
    (hT : GlobalTheory.LocAcyc.AbsIntClosed T) : IsIntegrallyClosed T := by
  rw [isIntegrallyClosed_iff (FractionRing T)]
  intro x hx
  obtain ⟨f, hf, h⟩ := hx
  exact exists_eq_of_aeval_eq_zero hT _ f hf rfl x (by rw [aeval_def]; exact h)

theorem isAlgClosed_fractionRing (T : Type) [CommRing T] [IsDomain T]
    (hT : GlobalTheory.LocAcyc.AbsIntClosed T) : IsAlgClosed (FractionRing T) := by
  first
  | exact @_root_.GlobalTheory.MonicRootRange.isAlgClosed_fractionRing
  | exact _root_.GlobalTheory.MonicRootRange.isAlgClosed_fractionRing
  | (apply _root_.GlobalTheory.MonicRootRange.isAlgClosed_fractionRing <;> assumption)
  | (intros; apply _root_.GlobalTheory.MonicRootRange.isAlgClosed_fractionRing <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MonicRootRange.isAlgClosed_fractionRing <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MonicRootRange.isAlgClosed_fractionRing ..)

end GlobalTheory.LocAcycEmbed

namespace GlobalTheory.LocAcycEmbed

theorem essFiniteType_int_of_finite_localization {A C A₁ : Type} [CommRing A] [CommRing C] [CommRing A₁]
    [Algebra A C] [Algebra C A₁] [Algebra.EssFiniteType ℤ A] [Module.Finite A C] (M : Submonoid C)
    [IsLocalization M A₁] : Algebra.EssFiniteType ℤ A₁ := by
  haveI : IsScalarTower ℤ A C := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [eq_intCast (algebraMap ℤ C), eq_intCast (algebraMap ℤ A), map_intCast])
  haveI : IsScalarTower ℤ C A₁ := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [eq_intCast (algebraMap ℤ A₁), eq_intCast (algebraMap ℤ C), map_intCast])
  haveI : Algebra.EssFiniteType A C := Algebra.EssFiniteType.of_finiteType A C
  haveI : Algebra.EssFiniteType C A₁ := Algebra.EssFiniteType.of_isLocalization A₁ M
  haveI : Algebra.EssFiniteType ℤ C := Algebra.EssFiniteType.comp ℤ A C
  exact Algebra.EssFiniteType.comp ℤ C A₁

theorem exists_fractionRing_hom {C A₁ : Type} [CommRing C] [IsDomain C] [CommRing A₁] [IsDomain A₁]
    [Algebra C A₁] (L : Type) [Field L] [Algebra C L] [IsFractionRing C L]
    (hinj : Function.Injective (algebraMap C A₁)) :
    ∃ κ : L →+* FractionRing A₁,
      κ.comp (algebraMap C L) = (algebraMap A₁ (FractionRing A₁)).comp (algebraMap C A₁) := by
  have hg : Function.Injective ((algebraMap A₁ (FractionRing A₁)).comp (algebraMap C A₁)) :=
    (IsFractionRing.injective A₁ (FractionRing A₁)).comp hinj
  refine ⟨IsFractionRing.lift (A := C) (K := L) hg, ?_⟩
  exact IsLocalization.lift_comp _

end GlobalTheory.LocAcycEmbed

namespace GlobalTheory.LocAcycEmbed

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem exists_normal_local_between : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i →
    ∀ (L : Type) [Field L] [Algebra (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
      [Algebra.IsSeparable (FractionRing A) L],
    ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (_ : IsNoetherianRing A₁)
      (_ : IsIntegrallyClosed A₁) (_ : Algebra.EssFiniteType ℤ A₁) (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective j ∧ Function.Injective i₁ ∧ IsLocalHom i₁ ∧ i₁.comp j = i ∧
      ∃ κ : L →+* FractionRing A₁,
        κ.comp ((algebraMap (FractionRing A) L).comp (algebraMap A (FractionRing A))) =
          (algebraMap A₁ (FractionRing A₁)).comp j := by
  intro T _ _ _ hT A _ _ _ _ _ _ i hi L _ _ _ _
  haveI : IsIntegrallyClosed T := isIntegrallyClosed_of_absIntClosed T hT
  haveI : IsAlgClosed (FractionRing T) := isAlgClosed_fractionRing T hT
  have hgi : Function.Injective ((algebraMap T (FractionRing T)).comp i) :=
    (IsFractionRing.injective T (FractionRing T)).comp hi
  let φ : FractionRing A →+* FractionRing T := IsFractionRing.lift hgi
  letI : Algebra (FractionRing A) (FractionRing T) := φ.toAlgebra
  let σ : L →ₐ[FractionRing A] FractionRing T := IsAlgClosed.lift
  letI : Algebra A L := ((algebraMap (FractionRing A) L).comp (algebraMap A (FractionRing A))).toAlgebra
  haveI : IsScalarTower A (FractionRing A) L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hAL : Function.Injective (algebraMap A L) :=
    (algebraMap (FractionRing A) L).injective.comp (IsFractionRing.injective A (FractionRing A))
  have h1 : (algebraMap T (FractionRing T)).comp i = (σ : L →+* FractionRing T).comp (algebraMap A L) := by
    ext a
    show algebraMap T (FractionRing T) (i a) = σ (algebraMap (FractionRing A) L (algebraMap A (FractionRing A) a))
    rw [σ.commutes]
    show _ = φ (algebraMap A (FractionRing A) a)
    rw [IsFractionRing.lift_algebraMap]
    rfl
  let C := integralClosure A L
  haveI : Module.Finite A C := IsIntegralClosure.finite A (FractionRing A) L C
  haveI : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  haveI : IsFractionRing C L := integralClosure.isFractionRing_of_finite_extension (FractionRing A) L
  haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing A)
  have hint : ∀ x : C, ∃ t : T, algebraMap T (FractionRing T) t = σ (x : L) := by
    intro x
    obtain ⟨f, hf, hfx⟩ := x.2
    apply exists_eq_of_aeval_eq_zero hT _ (f.map i) (hf.map i) rfl
    rw [aeval_def, eval₂_map, h1]
    have := Polynomial.hom_eval₂ f (algebraMap A L) (σ : L →+* FractionRing T) (x : L)
    rw [hfx, map_zero] at this
    exact this.symm
  choose ct hct using hint
  have hinjT := IsFractionRing.injective T (FractionRing T)
  let c : C →+* T :=
    { toFun := ct
      map_one' := hinjT (by rw [hct]; simp)
      map_mul' := fun x y => hinjT (by rw [hct, map_mul, hct, hct]; simp)
      map_zero' := hinjT (by rw [hct]; simp)
      map_add' := fun x y => hinjT (by rw [hct, map_add, hct, hct]; simp) }
  have hc : ∀ x, algebraMap T (FractionRing T) (c x) = σ (x : L) := hct
  have hcinj : Function.Injective c := by
    intro x y h
    have := congrArg (algebraMap T (FractionRing T)) h
    rw [hc, hc] at this
    exact Subtype.ext ((σ : L →+* FractionRing T).injective this)
  have hci : c.comp (algebraMap A C) = i := by
    ext a
    apply hinjT
    rw [RingHom.comp_apply, hc]
    exact (RingHom.congr_fun h1 a).symm
  let P : Ideal C := (maximalIdeal T).comap c
  haveI : P.IsPrime := Ideal.comap_isPrime c _
  have hunit : ∀ y : P.primeCompl, IsUnit (c y) := fun y => by
    by_contra h
    exact y.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  let i₁ : Localization.AtPrime P →+* T := IsLocalization.lift hunit
  let j : A →+* Localization.AtPrime P := (algebraMap C (Localization.AtPrime P)).comp (algebraMap A C)
  have hAC : Function.Injective (algebraMap A C) := fun x y h => hAL (congrArg Subtype.val h)
  have hCA₁ : Function.Injective (algebraMap C (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P)
  have hj : Function.Injective j := hCA₁.comp hAC
  have hi₁ : Function.Injective i₁ :=
    (IsLocalization.lift_injective_iff hunit).2 fun x y =>
      ⟨fun h => congrArg c (hCA₁ h), fun h => congrArg _ (hcinj h)⟩
  have hloc : IsLocalHom i₁ := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (S := Localization.AtPrime P) P.primeCompl x
    have e1 := IsLocalization.mk'_spec (Localization.AtPrime P) a s
    have e2 : IsUnit (c a) := by
      rw [← IsLocalization.lift_eq (S := Localization.AtPrime P) hunit a, ← e1, map_mul, IsLocalization.lift_eq (S := Localization.AtPrime P) hunit]
      exact hx.mul (hunit s)
    have ha : a ∈ P.primeCompl := fun h => ((IsLocalRing.mem_maximalIdeal _).1 h) e2
    exact isUnit_of_mul_isUnit_left (e1 ▸ IsLocalization.map_units (Localization.AtPrime P) ⟨a, ha⟩)
  have hcomp : i₁.comp j = i := by
    ext a
    show i₁ (algebraMap C _ (algebraMap A C a)) = i a
    rw [IsLocalization.lift_eq]
    exact RingHom.congr_fun hci a
  haveI : IsDomain (Localization.AtPrime P) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors P)
  haveI : IsIntegrallyClosed (Localization.AtPrime P) :=
    isIntegrallyClosed_of_isLocalization _ P.primeCompl (Ideal.primeCompl_le_nonZeroDivisors P)
  obtain ⟨κ, hκ⟩ := exists_fractionRing_hom (A₁ := Localization.AtPrime P) L hCA₁
  refine ⟨Localization.AtPrime P, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    essFiniteType_int_of_finite_localization (A := A) (C := C) P.primeCompl, j, i₁, hj, hi₁, hloc, hcomp, κ, ?_⟩
  ext a
  exact RingHom.congr_fun hκ (algebraMap A C a)

end GlobalTheory.LocAcycEmbed
