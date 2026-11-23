import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain
open IsLocalRing

namespace GlobalTheory.NormalApprox

variable {T : Type} [CommRing T]

abbrev gen (S : Finset T) : Subalgebra ℤ T := Algebra.adjoin ℤ (S : Set T)

def norm [IsDomain T] (S : Finset T) : Subring T where
  carrier := {x | IsIntegral (gen S) x ∧ ∃ s ∈ gen S, s ≠ 0 ∧ s * x ∈ gen S}
  mul_mem' := by
    rintro x y ⟨hx, s, hs, hs0, hsx⟩ ⟨hy, t, ht, ht0, hty⟩
    refine ⟨hx.mul hy, s * t, mul_mem hs ht, mul_ne_zero hs0 ht0, ?_⟩
    have e : s * t * (x * y) = (s * x) * (t * y) := by ring
    rw [e]; exact mul_mem hsx hty
  one_mem' := ⟨isIntegral_one, 1, one_mem _, one_ne_zero, by rw [mul_one]; exact one_mem _⟩
  add_mem' := by
    rintro x y ⟨hx, s, hs, hs0, hsx⟩ ⟨hy, t, ht, ht0, hty⟩
    refine ⟨hx.add hy, s * t, mul_mem hs ht, mul_ne_zero hs0 ht0, ?_⟩
    have e : s * t * (x + y) = t * (s * x) + s * (t * y) := by ring
    rw [e]; exact add_mem (mul_mem ht hsx) (mul_mem hs hty)
  zero_mem' := ⟨isIntegral_zero, 1, one_mem _, one_ne_zero, by rw [mul_zero]; exact zero_mem _⟩
  neg_mem' := by
    rintro x ⟨hx, s, hs, hs0, hsx⟩
    refine ⟨hx.neg, s, hs, hs0, ?_⟩
    rw [mul_neg]; exact neg_mem hsx

theorem mem_norm [IsDomain T] {S : Finset T} {x : T} :
    x ∈ norm S ↔ IsIntegral (gen S) x ∧ ∃ s ∈ gen S, s ≠ 0 ∧ s * x ∈ gen S := Iff.rfl

theorem gen_le_norm [IsDomain T] (S : Finset T) : (gen S).toSubring ≤ norm S := by
  intro x hx
  refine ⟨?_, 1, one_mem _, one_ne_zero, by rw [one_mul]; exact hx⟩
  have : x = algebraMap (gen S) T ⟨x, hx⟩ := rfl
  rw [this]; exact isIntegral_algebraMap

theorem norm_mono [IsDomain T] : Monotone (norm (T := T)) := by
  intro S S' h x ⟨hx, s, hs, hs0, hsx⟩
  have hle : gen S ≤ gen S' := Algebra.adjoin_mono (by exact_mod_cast h)
  letI : Algebra (gen S) (gen S') := (Subalgebra.inclusion hle).toAlgebra
  haveI : IsScalarTower (gen S) (gen S') T := .of_algebraMap_eq fun _ => rfl
  exact ⟨hx.tower_top, s, hle hs, hs0, hle hsx⟩

end GlobalTheory.NormalApprox

namespace GlobalTheory.NormalApprox

variable {T : Type} [CommRing T] [IsDomain T]

section Equiv

variable (S : Finset T)

instance : Algebra.FiniteType ℤ (gen S) := (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset _)

noncomputable def toFrac : FractionRing (gen S) →ₐ[gen S] FractionRing T :=
  IsFractionRing.liftAlgHom (g := Algebra.ofId (gen S) (FractionRing T))
    (by
    change Function.Injective (algebraMap (gen S) (FractionRing T))
    rw [IsScalarTower.algebraMap_eq (gen S) T (FractionRing T)]
    exact (IsFractionRing.injective T (FractionRing T)).comp Subtype.val_injective)

end Equiv

end GlobalTheory.NormalApprox

namespace GlobalTheory.NormalApprox

variable {T : Type} [CommRing T] [IsDomain T] (S : Finset T)

theorem toFrac_mk' (a : gen S) (s : nonZeroDivisors (gen S)) :
    toFrac S (IsLocalization.mk' (FractionRing (gen S)) a s) =
      algebraMap T (FractionRing T) a / algebraMap T (FractionRing T) (s : gen S) := by
  simp [toFrac, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_mk']
  rfl

theorem map_norm_eq [IsIntegrallyClosed T] :
    (norm S).map (algebraMap T (FractionRing T)) =
      ((toFrac S).comp (integralClosure (gen S) (FractionRing (gen S))).val).range.toSubring := by
  ext y
  simp only [Subring.mem_map, Subalgebra.mem_toSubring, AlgHom.mem_range]
  constructor
  · rintro ⟨x, ⟨hx, s, hs, hs0, hsx⟩, rfl⟩
    have hs0' : (⟨s, hs⟩ : gen S) ≠ 0 := fun h => hs0 (congrArg Subtype.val h)
    let k := IsLocalization.mk' (FractionRing (gen S)) (⟨s * x, hsx⟩ : gen S)
      (⟨⟨s, hs⟩, mem_nonZeroDivisors_of_ne_zero hs0'⟩ : nonZeroDivisors (gen S))
    have hsF : algebraMap T (FractionRing T) s ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective T (FractionRing T))).mpr hs0
    have hk : toFrac S k = algebraMap T (FractionRing T) x := by
      rw [toFrac_mk']
      change algebraMap T (FractionRing T) (s * x) / algebraMap T (FractionRing T) s = _
      rw [map_mul]
      field_simp
    refine ⟨⟨k, ?_⟩, hk⟩
    change IsIntegral (gen S) k
    rw [← isIntegral_algHom_iff (toFrac S) (toFrac S).toRingHom.injective, hk]
    exact hx.map (IsScalarTower.toAlgHom (gen S) T (FractionRing T))
  · rintro ⟨⟨c, hc⟩, rfl⟩
    have hi : IsIntegral (gen S) (toFrac S c) :=
      (isIntegral_algHom_iff _ (toFrac S).toRingHom.injective).mpr hc
    obtain ⟨t, ht⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := T) hi.tower_top
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (gen S)) c
    have hs0 : ((s : gen S) : T) ≠ 0 := fun h => nonZeroDivisors.ne_zero s.2 (Subtype.ext h)
    have hsF : algebraMap T (FractionRing T) ((s : gen S) : T) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective T (FractionRing T))).mpr hs0
    refine ⟨t, ⟨?_, (s : gen S), (s : gen S).2, hs0, ?_⟩, ht⟩
    · rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom (gen S) T (FractionRing T))
        (IsFractionRing.injective T _)]
      change IsIntegral _ (algebraMap T (FractionRing T) t)
      rw [ht]; exact hi
    · have e : ((s : gen S) : T) * t = (a : T) := by
        apply IsFractionRing.injective T (FractionRing T)
        rw [map_mul, ht]
        change _ * toFrac S (IsLocalization.mk' (FractionRing (gen S)) a s) = _
        rw [toFrac_mk']
        field_simp
      rw [e]; exact a.2

noncomputable def normEquiv [IsIntegrallyClosed T] :
    norm S ≃+* integralClosure (gen S) (FractionRing (gen S)) :=
  ((norm S).equivMapOfInjective _ (IsFractionRing.injective T (FractionRing T))).trans
    ((RingEquiv.subringCongr (map_norm_eq S)).trans
      (AlgEquiv.ofInjective _ (fun _ _ h => Subtype.ext ((toFrac S).toRingHom.injective h))).symm.toRingEquiv)

theorem norm_isNoetherianRing [IsIntegrallyClosed T] : IsNoetherianRing (norm S) := by
  haveI : IsNoetherianRing (gen S) := Algebra.FiniteType.isNoetherianRing ℤ _
  haveI := GlobalTheory.finite_integralClosure_of_essFiniteType_int (gen S)
  haveI : IsNoetherianRing (integralClosure (gen S) (FractionRing (gen S))) :=
    Algebra.FiniteType.isNoetherianRing (gen S) _
  exact isNoetherianRing_of_ringEquiv _ (normEquiv S).symm

theorem norm_isIntegrallyClosed [IsIntegrallyClosed T] : IsIntegrallyClosed (norm S) := by
  haveI : IsIntegrallyClosed (integralClosure (gen S) (FractionRing (gen S))) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing (gen S))
  exact IsIntegrallyClosed.of_equiv (normEquiv S).symm

end GlobalTheory.NormalApprox

namespace GlobalTheory.NormalApprox

variable {T : Type} [CommRing T] [IsDomain T]

def loc (S : Finset T) : Subring T where
  carrier := {x | ∃ s ∈ norm S, IsUnit s ∧ s * x ∈ norm S}
  mul_mem' := by
    rintro x y ⟨s, hs, hsu, hsx⟩ ⟨t, ht, htu, hty⟩
    refine ⟨s * t, mul_mem hs ht, hsu.mul htu, ?_⟩
    have e : s * t * (x * y) = (s * x) * (t * y) := by ring
    rw [e]; exact mul_mem hsx hty
  one_mem' := ⟨1, one_mem _, isUnit_one, by rw [mul_one]; exact one_mem _⟩
  add_mem' := by
    rintro x y ⟨s, hs, hsu, hsx⟩ ⟨t, ht, htu, hty⟩
    refine ⟨s * t, mul_mem hs ht, hsu.mul htu, ?_⟩
    have e : s * t * (x + y) = t * (s * x) + s * (t * y) := by ring
    rw [e]; exact add_mem (mul_mem ht hsx) (mul_mem hs hty)
  zero_mem' := ⟨1, one_mem _, isUnit_one, by rw [mul_zero]; exact zero_mem _⟩
  neg_mem' := by
    rintro x ⟨s, hs, hsu, hsx⟩
    exact ⟨s, hs, hsu, by rw [mul_neg]; exact neg_mem hsx⟩

theorem norm_le_loc (S : Finset T) : norm S ≤ loc S :=
  fun x hx => ⟨1, one_mem _, isUnit_one, by rw [one_mul]; exact hx⟩

theorem loc_mono : Monotone (loc (T := T)) := by
  intro S S' h x ⟨s, hs, hsu, hsx⟩
  exact ⟨s, norm_mono h hs, hsu, norm_mono h hsx⟩

theorem mem_loc_of_mem (S : Finset T) {x : T} (hx : x ∈ S) : x ∈ loc S :=
  norm_le_loc S (gen_le_norm S (Algebra.subset_adjoin (Finset.mem_coe.mpr hx)))

theorem isUnit_of_isUnit_coe (S : Finset T) (x : loc S) (hx : IsUnit (x : T)) : IsUnit x := by
  obtain ⟨s, hs, hsu, hsx⟩ := x.2
  obtain ⟨u, hu⟩ := hx
  have hau : IsUnit (s * (x : T)) := hsu.mul (hu ▸ u.isUnit)
  have hinv : ((u⁻¹ : Tˣ) : T) ∈ loc S := by
    refine ⟨s * (x : T), hsx, hau, ?_⟩
    rw [← hu, mul_assoc, Units.mul_inv, mul_one]; exact hs
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  change (x : T) * ((u⁻¹ : Tˣ) : T) = 1
  rw [← hu, Units.mul_inv]

theorem loc_isLocalRing [IsLocalRing T] (S : Finset T) : IsLocalRing (loc S) := by
  refine IsLocalRing.of_nonunits_add fun a b ha hb hab => ?_
  have ha' : (a : T) ∈ maximalIdeal T := fun h => ha (isUnit_of_isUnit_coe S a h)
  have hb' : (b : T) ∈ maximalIdeal T := fun h => hb (isUnit_of_isUnit_coe S b h)
  have : ((a + b : loc S) : T) ∈ maximalIdeal T := by
    rw [Subring.coe_add]; exact add_mem ha' hb'
  exact this (hab.map (loc S).subtype)

def unitsIn (S : Finset T) : Submonoid (norm S) :=
  (IsUnit.submonoid T).comap (norm S).subtype

theorem unitsIn_le (S : Finset T) : unitsIn S ≤ nonZeroDivisors (norm S) := fun s hs =>
  mem_nonZeroDivisors_of_ne_zero fun h => (hs : IsUnit (s : T)).ne_zero (by rw [h]; rfl)

instance (S : Finset T) : Algebra (norm S) (loc S) := (Subring.inclusion (norm_le_loc S)).toAlgebra

theorem loc_isLocalization (S : Finset T) : IsLocalization (unitsIn S) (loc S) := by
  refine ⟨fun y => isUnit_of_isUnit_coe S _ y.2, fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
  · obtain ⟨s, hs, hsu, hsx⟩ := z.2
    refine ⟨(⟨_, hsx⟩, ⟨⟨s, hs⟩, hsu⟩), Subtype.ext ?_⟩
    change (z : T) * s = s * z
    ring
  · have : (x : T) = y := congrArg (fun z : loc S => (z : T)) h
    rw [Subtype.ext this]

end GlobalTheory.NormalApprox

namespace GlobalTheory.NormalApprox

theorem exists_noetherian_normal_local_approx :
    ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], IsIntegrallyClosed T →
    ∃ 𝒜 : Finset T → Subring T, Monotone 𝒜 ∧ (∀ (S : Finset T), ∀ x ∈ S, x ∈ 𝒜 S) ∧
      ∀ S, IsNoetherianRing (𝒜 S) ∧ IsIntegrallyClosed (𝒜 S) ∧ IsLocalRing (𝒜 S) ∧
        ∀ x : 𝒜 S, IsUnit (x : T) → IsUnit x := by
  intro T _ _ _ hT
  refine ⟨loc, loc_mono, fun S x hx => mem_loc_of_mem S hx, fun S => ⟨?_, ?_, loc_isLocalRing S,
    isUnit_of_isUnit_coe S⟩⟩
  · haveI := loc_isLocalization S
    exact IsLocalization.isNoetherianRing (unitsIn S) _ (norm_isNoetherianRing S)
  · haveI := loc_isLocalization S
    haveI := norm_isIntegrallyClosed S
    exact isIntegrallyClosed_of_isLocalization (loc S) (unitsIn S) (unitsIn_le S)

end GlobalTheory.NormalApprox
