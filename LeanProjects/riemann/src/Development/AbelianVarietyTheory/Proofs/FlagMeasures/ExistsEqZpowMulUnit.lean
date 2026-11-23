import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.UnramVal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem zpow_mul_unit_mem_iff {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (k : ℤ) (u : (𝒪[F])ˣ) :
    (ϖ : F) ^ k * ((u : 𝒪[F]) : F) ∈ 𝒪[F] ↔ 0 ≤ k := by
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  constructor
  · intro h
    by_contra hk
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -((n : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
    refine hϖ.not_isUnit (IsUnit.of_mul_eq_one (ϖ ^ n * ⟨_, h⟩ * ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F])) ?_)
    apply Subtype.ext
    have hu : ((u : 𝒪[F]) : F) * (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    have h1 : (ϖ : F) * (ϖ : F) ^ n * (ϖ : F) ^ (-((n : ℤ) + 1)) = 1 := by
      rw [zpow_neg, zpow_add_one₀ h0, zpow_natCast]
      field_simp
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_one]
    linear_combination (((u : 𝒪[F]) : F) * (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F)) * h1 + hu
  · intro hk
    lift k to ℕ using hk
    rw [zpow_natCast]
    exact Subring.mul_mem _ (Subring.pow_mem _ ϖ.2 k) (u : 𝒪[F]).2

variable [IsNonarchimedeanLocalField F]

theorem vE_zpow_mul_unit (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (k : ℤ)
    (u : (𝒪[F])ˣ) : vE L ϖ (algebraMap F E ((ϖ : F) ^ k * ((u : 𝒪[F]) : F))) = k := by
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hset : {m : ℤ | ∃ y ∈ L.O, algebraMap F E ((ϖ : F) ^ k * ((u : 𝒪[F]) : F))
      = algebraMap F E ((ϖ : F) ^ m) * y} = Set.Iic k := by
    ext m
    have hsplit : (ϖ : F) ^ k * ((u : 𝒪[F]) : F)
        = (ϖ : F) ^ m * ((ϖ : F) ^ (k - m) * ((u : 𝒪[F]) : F)) := by
      rw [← mul_assoc, ← zpow_add₀ h0]; congr 2; ring
    have hun : IsUnit (algebraMap F E ((ϖ : F) ^ m)) :=
      (IsUnit.mk0 _ (zpow_ne_zero m h0)).map _
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    rw [hsplit, map_mul, ← sub_nonneg, ← zpow_mul_unit_mem_iff hϖ (k - m) u,
      ← GlobalTheory.UnramOrder.algebraMap_mem_iff L]
    constructor
    · rintro ⟨y, hy, h⟩
      rw [hun.mul_left_cancel h]; exact hy
    · intro h; exact ⟨_, h, rfl⟩
  rw [vE, hset, csSup_Iic]

theorem exists_eq_zpow_mul_unit {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {x : F} (hx : x ≠ 0) :
    ∃ (k : ℤ) (u : (𝒪[F])ˣ), x = (ϖ : F) ^ k * ((u : 𝒪[F]) : F) := by
  obtain ⟨k, u, h⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ hx
  refine ⟨k, u, ?_⟩
  rw [h, mul_comm]; rfl

theorem vE_valuation : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → (∀ x y : F, x ≠ 0 → y ≠ 0 → vE L ϖ (algebraMap F E (x * y)) = vE L ϖ (algebraMap F E x) + vE L ϖ (algebraMap F E y)) ∧ vE L ϖ (algebraMap F E (ϖ : F)) = 1 ∧ (∀ x : F, x ≠ 0 → (0 ≤ vE L ϖ (algebraMap F E x) ↔ x ∈ 𝒪[F])) ∧ (∀ x : F, x ≠ 0 → ∃ u : (𝒪[F])ˣ, x = (ϖ : F) ^ (vE L ϖ (algebraMap F E x)) * ((u : 𝒪[F]) : F)) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  refine ⟨fun x y hx hy => ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨k, u, rfl⟩ := exists_eq_zpow_mul_unit hϖ hx
    obtain ⟨l, v, rfl⟩ := exists_eq_zpow_mul_unit hϖ hy
    have : (ϖ : F) ^ k * ((u : 𝒪[F]) : F) * ((ϖ : F) ^ l * ((v : 𝒪[F]) : F))
        = (ϖ : F) ^ (k + l) * (((u * v : (𝒪[F])ˣ) : 𝒪[F]) : F) := by
      rw [zpow_add₀ h0, Units.val_mul, Subring.coe_mul]; ring
    rw [this, vE_zpow_mul_unit L hϖ, vE_zpow_mul_unit L hϖ, vE_zpow_mul_unit L hϖ]
  · simpa using vE_zpow_mul_unit L hϖ 1 1
  · obtain ⟨k, u, rfl⟩ := exists_eq_zpow_mul_unit hϖ hx
    rw [vE_zpow_mul_unit L hϖ, zpow_mul_unit_mem_iff hϖ]
  · obtain ⟨k, u, rfl⟩ := exists_eq_zpow_mul_unit hϖ hx
    exact ⟨u, by rw [vE_zpow_mul_unit L hϖ]⟩

end GlobalTheory.UnramVal
