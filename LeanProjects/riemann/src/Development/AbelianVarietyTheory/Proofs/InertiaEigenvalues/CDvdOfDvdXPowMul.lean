import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX

noncomputable section

open PowerSeries GlobalTheory.NB.LT

namespace GlobalTheory.NB.LT.EEBasic

section General
variable {B : Type} [CommRing B] (b : B)

theorem pow_dvd_iff_eval (k : ℕ) (x : AdicCompletion (Ideal.span {b}) B) :
    (algebraMap B (AdicCompletion (Ideal.span {b}) B) b) ^ k ∣ x ↔
      AdicCompletion.eval (Ideal.span {b}) B k x = 0 := by
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval
    (Submodule.fg_span_singleton b), Ideal.smul_top_eq_map, Submodule.restrictScalars_mem,
    Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton,
    map_pow]

theorem eval_algebraMap (k : ℕ) (c : B) :
    AdicCompletion.eval (Ideal.span {b}) B k (algebraMap B (AdicCompletion (Ideal.span {b}) B) c)
      = Submodule.Quotient.mk c := by
  rw [AdicCompletion.algebraMap_apply]
  rfl

theorem pow_dvd_of_pow_dvd (k : ℕ) (c : B)
    (h : (algebraMap B (AdicCompletion (Ideal.span {b}) B) b) ^ k ∣
      algebraMap B (AdicCompletion (Ideal.span {b}) B) c) : b ^ k ∣ c := by
  rw [pow_dvd_iff_eval, eval_algebraMap, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
    Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  exact h

theorem exists_pow_dvd_sub (k : ℕ) (x : AdicCompletion (Ideal.span {b}) B) :
    ∃ c : B, (algebraMap B (AdicCompletion (Ideal.span {b}) B) b) ^ k ∣
      x - algebraMap B (AdicCompletion (Ideal.span {b}) B) c := by
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _
    (AdicCompletion.eval (Ideal.span {b}) B k x)
  exact ⟨c, by rw [pow_dvd_iff_eval, map_sub, eval_algebraMap, hc, sub_self]⟩

theorem complete : IsAdicComplete
    (Ideal.span {algebraMap B (AdicCompletion (Ideal.span {b}) B) b})
    (AdicCompletion (Ideal.span {b}) B) := by
  have h : Ideal.span {algebraMap B (AdicCompletion (Ideal.span {b}) B) b} =
      (Ideal.span {b}).map (algebraMap B (AdicCompletion (Ideal.span {b}) B)) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [h, IsAdicComplete.map_algebraMap_iff]
  exact AdicCompletion.isAdicComplete (Submodule.fg_span_singleton b)

end General

variable {O : Type} [CommRing O]

theorem C_dvd_iff (c : O) (a : O⟦X⟧) : C c ∣ a ↔ ∀ n, c ∣ coeff n a := by
  constructor
  · rintro ⟨q, rfl⟩ n
    rw [coeff_C_mul]
    exact dvd_mul_right _ _
  · intro h
    choose q hq using h
    exact ⟨PowerSeries.mk q, PowerSeries.ext fun n => by rw [coeff_C_mul, coeff_mk, hq]⟩

theorem C_dvd_of_dvd_X_pow_mul (c : O) (m : ℕ) (a : O⟦X⟧) (h : C c ∣ X ^ m * a) : C c ∣ a := by
  rw [C_dvd_iff] at h ⊢
  intro n
  have := h (n + m)
  rwa [coeff_X_pow_mul] at this

theorem C_dvd_of_dvd_away (c : O) (a : O⟦X⟧)
    (h : algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) (C c) ∣
      algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) a) : C c ∣ a := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨m, q, hq⟩ := IsLocalization.Away.surj (X : O⟦X⟧) z
  have h1 : algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) (X ^ m * a) =
      algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) (C c * q) := by
    rw [map_mul, map_mul, map_pow, hz, ← hq]; ring
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (X : O⟦X⟧) h1
  refine C_dvd_of_dvd_X_pow_mul c (n + m) a ⟨X ^ n * q, ?_⟩
  rw [pow_add, mul_assoc, hn]; ring

theorem algebraMap_EE (l : ℕ) (a : O⟦X⟧) : algebraMap O⟦X⟧ (EE O l) a =
    algebraMap (Localization.Away (X : O⟦X⟧)) (EE O l)
      (algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) a) := by
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply]; rfl

theorem saturated (l : ℕ) (a : O⟦X⟧) (k : ℕ)
    (h : (l : EE O l) ^ k ∣ algebraMap O⟦X⟧ (EE O l) a) : (l : O⟦X⟧) ^ k ∣ a := by
  rw [algebraMap_EE, ← map_natCast (algebraMap (Localization.Away (X : O⟦X⟧)) (EE O l)) l] at h
  have h2 := pow_dvd_of_pow_dvd _ k _ h
  have e : (l : O⟦X⟧) ^ k = C ((l : O) ^ k) := by rw [map_pow, map_natCast]
  rw [e]
  apply C_dvd_of_dvd_away
  rwa [← e, map_pow, map_natCast]

end GlobalTheory.NB.LT.EEBasic

namespace GlobalTheory.NB.LT

open EEBasic

theorem EE_basic : ∀ {l : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O], l.Prime → ¬ IsUnit (l : O) → Function.Injective (algebraMap O⟦X⟧ (EE O l)) ∧ IsUnit (algebraMap O⟦X⟧ (EE O l) X) ∧ IsAdicComplete (Ideal.span {(l : EE O l)}) (EE O l) ∧ (∀ (x : EE O l) (k : ℕ), ∃ (a : O⟦X⟧) (m : ℕ), (l : EE O l) ^ k ∣ x * algebraMap O⟦X⟧ (EE O l) (X ^ m) - algebraMap O⟦X⟧ (EE O l) a) ∧ (∀ (a : O⟦X⟧) (k : ℕ), (l : EE O l) ^ k ∣ algebraMap O⟦X⟧ (EE O l) a → (l : O⟦X⟧) ^ k ∣ a) := by
  intro l O _ _ _ _ _ _ hl
  refine ⟨?_, ?_, ?_, ?_, saturated l⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    refine PowerSeries.ext fun n => ?_
    rw [map_zero]
    refine IsHausdorff.haus (I := IsLocalRing.maximalIdeal O) inferInstance _ fun k => ?_
    have h1 := saturated l a k (by rw [ha]; exact dvd_zero _)
    have e : (l : O⟦X⟧) ^ k = C ((l : O) ^ k) := by rw [map_pow, map_natCast]
    rw [e, C_dvd_iff] at h1
    obtain ⟨q, hq⟩ := h1 n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hq]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ((IsLocalRing.mem_maximalIdeal _).2 hl) k)
  · rw [algebraMap_EE]
    exact (IsLocalization.Away.algebraMap_isUnit (X : O⟦X⟧)).map _
  · have := complete (l : Localization.Away (X : O⟦X⟧))
    rwa [map_natCast] at this
  · intro x k
    obtain ⟨c, hc⟩ := exists_pow_dvd_sub (l : Localization.Away (X : O⟦X⟧)) k x
    rw [map_natCast] at hc
    obtain ⟨m, q, hq⟩ := IsLocalization.Away.surj (X : O⟦X⟧) c
    refine ⟨q, m, ?_⟩
    rw [algebraMap_EE l q, ← hq, map_mul, algebraMap_EE, map_pow (algebraMap O⟦X⟧ _), ← sub_mul]
    exact hc.mul_right _

end GlobalTheory.NB.LT
