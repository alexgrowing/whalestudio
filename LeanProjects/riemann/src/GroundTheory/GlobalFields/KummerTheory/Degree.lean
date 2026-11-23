import Mathlib
import GroundTheory.ProfiniteCohomology.KummerBasic
import GroundTheory.ProfiniteCohomology.KummerFinite
import GroundTheory.ProfiniteCohomology.KummerCorrespondence

namespace GroundTheory.Global

open GroundTheory.ProfCoh IntermediateField

section Radicals

variable (K : Type*) [Field K] (n : ℕ)

def radicalClasses (Δ : Subgroup Kˣ) : Subgroup (UnitsModPow K n) :=
  Δ.map (QuotientGroup.mk' (unitsPow K n))

noncomputable def toRadicalClasses (Δ : Subgroup Kˣ) : Δ →* radicalClasses K n Δ :=
  ((QuotientGroup.mk' (unitsPow K n)).comp Δ.subtype).codRestrict _
    (fun a => Subgroup.mem_map_of_mem _ a.2)

lemma toRadicalClasses_surjective (Δ : Subgroup Kˣ) :
    Function.Surjective (toRadicalClasses K n Δ) := by
  rintro ⟨x, a, ha, rfl⟩
  exact ⟨⟨a, ha⟩, rfl⟩

lemma ker_toRadicalClasses (Δ : Subgroup Kˣ) :
    (toRadicalClasses K n Δ).ker = (unitsPow K n).subgroupOf Δ := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff (N := unitsPow K n)]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

noncomputable def radicalQuotientEquiv (Δ : Subgroup Kˣ) :
    (Δ ⧸ (unitsPow K n).subgroupOf Δ) ≃* radicalClasses K n Δ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_toRadicalClasses K n Δ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (toRadicalClasses_surjective K n Δ))

@[simp] lemma radicalQuotientEquiv_mk (Δ : Subgroup Kˣ) (a : Δ) :
    (radicalQuotientEquiv K n Δ (a : Δ ⧸ (unitsPow K n).subgroupOf Δ) : UnitsModPow K n) =
      ((a : Kˣ) : UnitsModPow K n) :=
  rfl

def kummerExtension (Ω : Type*) [Field Ω] [Algebra K Ω] (Δ : Subgroup Kˣ) :
    IntermediateField K Ω :=
  adjoin K {α : Ω | ∃ a ∈ Δ, α ^ n = algebraMap K Ω a}

theorem kummerExtension_eq_kummerField (Ω : Type*) [Field Ω] [Algebra K Ω] (Δ : Subgroup Kˣ) :
    kummerExtension K n Ω Δ = kummerField K n Ω (radicalClasses K n Δ) := by
  apply le_antisymm
  · rw [kummerExtension, adjoin_le_iff]
    rintro α ⟨a, ha, hα⟩
    exact subset_adjoin _ _ ⟨a, Subgroup.mem_map_of_mem _ ha, hα⟩
  · rw [kummerField, adjoin_le_iff]
    rintro α ⟨a, ⟨b, hb, hab⟩, hα⟩

    obtain ⟨c, hc⟩ := mem_unitsPow.mp (QuotientGroup.eq.mp hab)
    have hc0 : algebraMap K Ω (c : K) ≠ 0 := (map_ne_zero (algebraMap K Ω)).mpr c.ne_zero
    have ha : (a : K) = (b : K) * (c : K) ^ n := by
      have h1 : (c : K) ^ n = (b : K)⁻¹ * (a : K) := by
        simpa only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val]
          using congrArg Units.val hc
      rw [h1, ← mul_assoc, mul_inv_cancel₀ b.ne_zero, one_mul]
    have hβ : (α / algebraMap K Ω (c : K)) ^ n = algebraMap K Ω (b : K) := by
      rw [div_pow, hα, ha, map_mul, map_pow]
      field_simp
    have hmem : α / algebraMap K Ω (c : K) ∈ kummerExtension K n Ω Δ :=
      subset_adjoin _ _ ⟨b, hb, hβ⟩
    have : α = α / algebraMap K Ω (c : K) * algebraMap K Ω (c : K) := by field_simp
    rw [SetLike.mem_coe, this]
    exact mul_mem hmem (IntermediateField.algebraMap_mem _ _)

end Radicals

section Main

variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (Ω : Type*) [Field Ω] [Algebra K Ω] (Δ : Subgroup Kˣ)

instance kummerExtension_isGalois : IsGalois K (kummerExtension K n Ω Δ) := by
  rw [kummerExtension_eq_kummerField]
  exact kummerField_isGalois K n Ω _

instance kummerExtension_isMulCommutative : IsMulCommutative Gal(kummerExtension K n Ω Δ/K) := by
  rw [kummerExtension_eq_kummerField]
  exact kummerField_isMulCommutative K n Ω _

theorem kummerExtension_exponent_dvd : Monoid.exponent Gal(kummerExtension K n Ω Δ/K) ∣ n := by
  rw [kummerExtension_eq_kummerField]
  exact kummerField_exponent_dvd K n Ω _

instance finite_radicalClasses [Finite (Δ ⧸ (unitsPow K n).subgroupOf Δ)] :
    Finite (radicalClasses K n Δ) :=
  Finite.of_equiv _ (radicalQuotientEquiv K n Δ).toEquiv

variable [IsSepClosed Ω]

theorem kummerGroup_kummerExtension :
    kummerGroup K n (kummerExtension K n Ω Δ) = radicalClasses K n Δ := by
  rw [kummerExtension_eq_kummerField]
  exact kummerGroup_kummerField K n Ω _

theorem unitsPowIn_kummerExtension (hΔ : unitsPow K n ≤ Δ) :
    unitsPowIn K n (kummerExtension K n Ω Δ) = Δ := by
  have h1 : (QuotientGroup.mk' (unitsPow K n)).ker ≤ unitsPowIn K n (kummerExtension K n Ω Δ) := by
    rw [QuotientGroup.ker_mk']
    exact unitsPow_le_unitsPowIn K n _
  have h2 : (QuotientGroup.mk' (unitsPow K n)).ker ≤ Δ := by
    rw [QuotientGroup.ker_mk']
    exact hΔ
  calc unitsPowIn K n (kummerExtension K n Ω Δ)
      = (kummerGroup K n (kummerExtension K n Ω Δ)).comap (QuotientGroup.mk' (unitsPow K n)) :=
        (Subgroup.comap_map_eq_self h1).symm
    _ = (radicalClasses K n Δ).comap (QuotientGroup.mk' (unitsPow K n)) := by
        rw [kummerGroup_kummerExtension]
    _ = Δ := Subgroup.comap_map_eq_self h2

variable [Finite (Δ ⧸ (unitsPow K n).subgroupOf Δ)]

instance kummerExtension_finiteDimensional : FiniteDimensional K (kummerExtension K n Ω Δ) := by
  rw [kummerExtension_eq_kummerField]
  exact finiteDimensional_kummerField K n Ω _

theorem finrank_kummerExtension :
    Module.finrank K (kummerExtension K n Ω Δ) = Nat.card (Δ ⧸ (unitsPow K n).subgroupOf Δ) := by
  rw [kummerExtension_eq_kummerField, finrank_kummerField,
    Nat.card_congr (radicalQuotientEquiv K n Δ).toEquiv]

noncomputable def radicalQuotientEquivKummerGroup :
    (Δ ⧸ (unitsPow K n).subgroupOf Δ) ≃* kummerGroup K n (kummerExtension K n Ω Δ) :=
  (radicalQuotientEquiv K n Δ).trans
    (MulEquiv.subgroupCongr (kummerGroup_kummerExtension K n Ω Δ).symm)

noncomputable def kummerExtensionGalEquiv :
    Gal(kummerExtension K n Ω Δ/K) ≃* ((Δ ⧸ (unitsPow K n).subgroupOf Δ) →* rootsOfUnity n K) :=
  (galEquivDual K n (kummerExtension K n Ω Δ) (kummerExtension_exponent_dvd K n Ω Δ)).trans
    (MulEquiv.monoidHomCongrLeft (radicalQuotientEquivKummerGroup K n Ω Δ).symm)

end Main

section Converse

variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (Ω : Type*) [Field Ω] [Algebra K Ω]

end Converse

end GroundTheory.Global
