import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.PB

open PowerSeries

section Ext

variable {R S : Type*} [CommRing R] [CommRing S]

theorem X_pow_dvd_pow_of_nil (a : S⟦X⟧) (ha : IsNilpotent (constantCoeff a)) (m : ℕ) :
    ∃ N, (X : S⟦X⟧) ^ m ∣ a ^ N := by
  obtain ⟨n, hn⟩ := ha
  refine ⟨n * m, ?_⟩
  rw [pow_mul]
  exact pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr (by rw [_root_.map_pow, hn])) m

theorem ringHom_ext_nil {h₁ h₂ : R⟦X⟧ →+* S⟦X⟧} (hC : ∀ r, h₁ (C r) = h₂ (C r)) (hX : h₁ X = h₂ X)
    (hnil : IsNilpotent (constantCoeff (h₁ X))) : h₁ = h₂ := by
  have hpoly : ∀ p : Polynomial R, h₁ (p : R⟦X⟧) = h₂ (p : R⟦X⟧) := by
    intro p
    refine Polynomial.induction_on p (fun a => ?_) (fun p q hp hq => ?_) (fun n a _ => ?_)
    · rw [Polynomial.coe_C]
      exact hC a
    · rw [Polynomial.coe_add, _root_.map_add, _root_.map_add, hp, hq]
    · rw [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X,
        _root_.map_mul, _root_.map_mul, _root_.map_pow, _root_.map_pow, hC, hX]
  refine RingHom.ext fun F => sub_eq_zero.mp (PowerSeries.ext fun m => ?_)
  obtain ⟨N, hN⟩ := X_pow_dvd_pow_of_nil (h₁ X) hnil (m + 1)
  obtain ⟨G, hG⟩ : (X : R⟦X⟧) ^ N ∣ F - (PowerSeries.trunc N F : R⟦X⟧) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro i hi
    rw [_root_.map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hi, sub_self]
  have hd : h₁ F - h₂ F = h₁ X ^ N * (h₁ G - h₂ G) := by
    have hF : F = (PowerSeries.trunc N F : R⟦X⟧) + X ^ N * G := by rw [← hG]; ring
    rw [hF]
    simp only [_root_.map_add, _root_.map_mul, _root_.map_pow, hpoly, ← hX]
    ring
  have hdvd : (X : S⟦X⟧) ^ (m + 1) ∣ h₁ F - h₂ F := by
    rw [hd]
    exact dvd_mul_of_dvd_left hN _
  rw [_root_.map_zero]
  exact PowerSeries.X_pow_dvd_iff.mp hdvd m (Nat.lt_succ_self m)

end Ext

section Inj

variable {R : Type*} [CommRing R] [IsDomain R]

private theorem powerSeries_algHom_C {R : Type*} [CommRing R] (ψ : R⟦X⟧ →ₐ[R] R⟦X⟧) (c : R) :
    ψ (C c) = C c := by
  have h := ψ.commutes c
  rwa [PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h

private theorem constantCoeff_algHom_apply_of_constantCoeff_X {R : Type*} [CommRing R] (ψ : R⟦X⟧ →ₐ[R] R⟦X⟧)
    (h0 : constantCoeff (ψ X) = 0) (F : R⟦X⟧) : constantCoeff (ψ F) = constantCoeff F := by
  obtain ⟨G, hG⟩ : (X : R⟦X⟧) ∣ F - C (constantCoeff F) := by
    rw [PowerSeries.X_dvd_iff, _root_.map_sub, PowerSeries.constantCoeff_C, sub_self]
  have hF : F = C (constantCoeff F) + X * G := by rw [← hG]; ring
  rw [hF]
  first
  | simp only [_root_.map_add, _root_.map_mul, powerSeries_algHom_C, h0, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_X, zero_mul, add_zero]
  | simp [powerSeries_algHom_C, h0]

private theorem powerSeries_algHom_injective_of_X_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    (ψ : R⟦X⟧ →ₐ[R] R⟦X⟧) (h0 : constantCoeff (ψ X) = 0) (hne : ψ X ≠ 0) :
    Function.Injective ψ := by
  rw [injective_iff_map_eq_zero]
  intro F hF
  by_contra hF0
  have hex : ∃ n, coeff n F ≠ 0 := by
    by_contra h
    push_neg at h
    exact hF0 (PowerSeries.ext fun n => by rw [h n, _root_.map_zero])
  classical
  obtain ⟨n, hn, hmin⟩ : ∃ n, coeff n F ≠ 0 ∧ ∀ i < n, coeff i F = 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => by
      by_contra h
      exact Nat.find_min hex hi h⟩
  obtain ⟨U, hU⟩ : (X : R⟦X⟧) ^ n ∣ F := PowerSeries.X_pow_dvd_iff.mpr hmin
  have hU0 : constantCoeff U ≠ 0 := by
    intro h
    apply hn
    rw [hU]
    first
    | rw [PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, h]
    | simp [PowerSeries.coeff_X_pow_mul', h]
    | (rw [mul_comm]; simpa [h] using PowerSeries.coeff_mul_X_pow U n 0)
  have hψU : ψ U ≠ 0 := by
    intro h
    apply hU0
    rw [← constantCoeff_algHom_apply_of_constantCoeff_X ψ h0 U, h, _root_.map_zero]
  rw [hU, _root_.map_mul, _root_.map_pow] at hF
  exact mul_ne_zero (pow_ne_zero _ hne) hψU hF

private theorem substAlgHom_X_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {a : S⟦X⟧} (ha : HasSubst a) : (substAlgHom ha : R⟦X⟧ →ₐ[R] S⟦X⟧) X = a := by
  first
  | exact substAlgHom_X ha
  | exact subst_X ha
  | (rw [coe_substAlgHom]; exact subst_X ha)
  | (rw [substAlgHom_apply]; exact subst_X ha)
  | simp [coe_substAlgHom, subst_X ha]

theorem subst_injective {a : R⟦X⟧} (ha0 : constantCoeff a = 0) (hane : a ≠ 0) :
    Function.Injective (substAlgHom (HasSubst.of_constantCoeff_zero' ha0) : R⟦X⟧ →ₐ[R] R⟦X⟧) := by
  refine powerSeries_algHom_injective_of_X_ne_zero _ ?_ ?_
  · rw [substAlgHom_X_eq]
    exact ha0
  · rw [substAlgHom_X_eq]
    exact hane

end Inj

theorem constantCoeff_substAlgHom {R : Type*} [CommRing R] {a : R⟦X⟧} (ha0 : constantCoeff a = 0)
    (F : R⟦X⟧) :
    constantCoeff ((substAlgHom (HasSubst.of_constantCoeff_zero' ha0) : R⟦X⟧ →ₐ[R] R⟦X⟧) F) =
      constantCoeff F := by
  refine constantCoeff_algHom_apply_of_constantCoeff_X _ ?_ F
  rw [substAlgHom_X_eq]
  exact ha0

theorem algC {R : Type*} [CommRing R] (ψ : R⟦X⟧ →ₐ[R] R⟦X⟧) (c : R) : ψ (C c) = C c :=
  powerSeries_algHom_C ψ c

section Shift

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

abbrev Qk (O : Type*) [CommRing O] [IsLocalRing O] (k : ℕ) : Type _ :=
  O ⧸ (IsLocalRing.maximalIdeal O) ^ k

abbrev mkk (k : ℕ) : O →+* Qk O k := Ideal.Quotient.mk _

omit [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
theorem smod_iff {a : ℕ} {x y : O} :
    x ≡ y [SMOD ((IsLocalRing.maximalIdeal O) ^ a • ⊤ : Submodule O O)] ↔ mkk a x = mkk a y := by
  first
  | (rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]; exact Ideal.Quotient.eq.symm)
  | (rw [SModEq.sub_mem, Ideal.smul_top_eq_map]; simp [Ideal.Quotient.eq])
  | simp [SModEq.sub_mem, Ideal.Quotient.eq]

theorem ext_k {G G' : O⟦X⟧} (h : ∀ k, map (mkk k) G = map (mkk k) G') : G = G' := by
  refine PowerSeries.ext fun m => ?_
  have hk : ∀ k, coeff m G ≡ coeff m G' [SMOD ((IsLocalRing.maximalIdeal O) ^ k • ⊤ : Submodule O O)] := by
    intro k
    rw [smod_iff, ← PowerSeries.coeff_map, ← PowerSeries.coeff_map, h k]
  first
  | exact (IsHausdorff.eq_iff_smodEq (I := IsLocalRing.maximalIdeal O)).mpr hk
  | exact sub_eq_zero.mp (IsHausdorff.haus inferInstance _ fun k =>
      SModEq.sub_mem.mpr (by rw [sub_zero]; exact SModEq.sub_mem.mp (hk k)))

variable (t : O) (ht : t ∈ IsLocalRing.maximalIdeal O)
include ht

omit [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
theorem nil_k (k : ℕ) : IsNilpotent (constantCoeff ((X : (Qk O k)⟦X⟧) + C (mkk k t))) := by
  rw [_root_.map_add, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C, zero_add]
  refine ⟨k, ?_⟩
  rw [← _root_.map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow ht k)

omit [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
theorem hasSubst_k (k : ℕ) : HasSubst ((X : (Qk O k)⟦X⟧) + C (mkk k t)) := by
  first
  | exact nil_k t ht k
  | exact HasSubst.of_constantCoeff_nilpotent (nil_k t ht k)
  | exact HasSubst.of_constantCoeff_nilpotent (by simpa using nil_k t ht k)
  | (unfold HasSubst; exact nil_k t ht k)

def τk (k : ℕ) : O⟦X⟧ →ₐ[O] (Qk O k)⟦X⟧ := substAlgHom (hasSubst_k t ht k)

omit [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
theorem τk_X (k : ℕ) : τk t ht k X = X + C (mkk k t) := by
  show (substAlgHom (hasSubst_k t ht k) : O⟦X⟧ →ₐ[O] (Qk O k)⟦X⟧) X = _
  exact substAlgHom_X_eq _

omit [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
theorem τk_C (k : ℕ) (r : O) : τk t ht k (C r) = C (mkk k r) := by
  have h := (τk t ht k).commutes r
  rwa [PowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, Ideal.Quotient.algebraMap_eq] at h

omit [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
theorem τk_compat {k k' : ℕ} (hkk : k ≤ k') :
    (map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal O) hkk))).comp
      (τk t ht k').toRingHom = (τk t ht k).toRingHom := by
  symm
  refine ringHom_ext_nil (fun r => ?_) ?_ ?_
  · show τk t ht k (C r) = map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal O) hkk)) (τk t ht k' (C r))
    rw [τk_C, τk_C, PowerSeries.map_C]
    first
    | exact congrArg C (Ideal.Quotient.factor_mk _ r).symm
    | rfl
  · show τk t ht k X = map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal O) hkk)) (τk t ht k' X)
    rw [τk_X, τk_X, _root_.map_add, PowerSeries.map_X, PowerSeries.map_C]
    first
    | rw [Ideal.Quotient.factor_mk]
    | rfl
  · show IsNilpotent (constantCoeff (τk t ht k X))
    rw [τk_X]
    exact nil_k t ht k

theorem exists_lim (F : O⟦X⟧) (m : ℕ) : ∃ L : O, ∀ k, mkk k L = coeff m (τk t ht k F) := by
  choose x hx using fun k => Ideal.Quotient.mk_surjective (coeff m (τk t ht k F))
  have hcompat : ∀ {a b : ℕ}, a ≤ b →
      x a ≡ x b [SMOD ((IsLocalRing.maximalIdeal O) ^ a • ⊤ : Submodule O O)] := by
    intro a b hab
    have h : coeff m (map (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal O) hab))
        (τk t ht b F)) = coeff m (τk t ht a F) :=
      congrArg (coeff m) (RingHom.congr_fun (τk_compat t ht hab) F)
    rw [PowerSeries.coeff_map, ← hx b] at h
    rw [smod_iff]
    refine (hx a).trans (h.symm.trans ?_)
    first
    | exact Ideal.Quotient.factor_mk _ _
    | rfl
  obtain ⟨L, hL⟩ : ∃ L : O, ∀ n,
      x n ≡ L [SMOD ((IsLocalRing.maximalIdeal O) ^ n • ⊤ : Submodule O O)] := by
    first
    | exact IsPrecomplete.prec inferInstance hcompat
    | exact IsPrecomplete.prec' _ hcompat
    | exact IsPrecomplete.prec inferInstance (fun h => hcompat h)
  exact ⟨L, fun k => ((smod_iff.mp (hL k)).symm).trans (hx k)⟩

def shiftFun (F : O⟦X⟧) : O⟦X⟧ := mk fun m => (exists_lim t ht F m).choose

theorem map_shiftFun (k : ℕ) (F : O⟦X⟧) : map (mkk k) (shiftFun t ht F) = τk t ht k F := by
  ext m
  rw [PowerSeries.coeff_map, shiftFun, PowerSeries.coeff_mk]
  exact (exists_lim t ht F m).choose_spec k

def shift : O⟦X⟧ →ₐ[O] O⟦X⟧ where
  toFun := shiftFun t ht
  map_one' := ext_k fun k => by rw [map_shiftFun, _root_.map_one, _root_.map_one]
  map_mul' F G := ext_k fun k => by
    rw [map_shiftFun, _root_.map_mul, _root_.map_mul, map_shiftFun, map_shiftFun]
  map_zero' := ext_k fun k => by rw [map_shiftFun, _root_.map_zero, _root_.map_zero]
  map_add' F G := ext_k fun k => by
    rw [map_shiftFun, _root_.map_add, _root_.map_add, map_shiftFun, map_shiftFun]
  commutes' r := ext_k fun k => by
    rw [map_shiftFun, AlgHom.commutes, PowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, map_C, Ideal.Quotient.algebraMap_eq]

theorem map_shift (k : ℕ) (F : O⟦X⟧) : map (mkk k) (shift t ht F) = τk t ht k F := map_shiftFun t ht k F

theorem shift_X : shift t ht X = X + C t := ext_k fun k => by
  rw [map_shift, τk_X, _root_.map_add, PowerSeries.map_X, PowerSeries.map_C]

theorem shift_shift (F : O⟦X⟧) : shift (-t) (neg_mem ht) (shift t ht F) = F := by
  refine ext_k fun k => ?_
  rw [map_shift]
  have key : (τk (-t) (neg_mem ht) k).toRingHom.comp (shift t ht).toRingHom =
      map (mkk k) := by
    refine (ringHom_ext_nil (h₁ := map (mkk k)) (fun r => ?_) ?_ ?_).symm
    · show map (mkk k) (C r) = τk (-t) (neg_mem ht) k (shift t ht (C r))
      rw [PowerSeries.map_C, algC, τk_C]
    · show map (mkk k) X = τk (-t) (neg_mem ht) k (shift t ht X)
      rw [PowerSeries.map_X, shift_X, _root_.map_add, τk_X, τk_C,
        _root_.map_neg, _root_.map_neg]
      ring
    · rw [PowerSeries.map_X, PowerSeries.constantCoeff_X]
      exact IsNilpotent.zero
  exact RingHom.congr_fun key F

omit ht in
theorem shift_congr {t t' : O} (h : t = t') (ht : t ∈ IsLocalRing.maximalIdeal O)
    (ht' : t' ∈ IsLocalRing.maximalIdeal O) : shift t ht = shift t' ht' := by
  subst h
  rfl

def shiftEquiv : O⟦X⟧ ≃ₐ[O] O⟦X⟧ :=
  AlgEquiv.ofAlgHom (shift t ht) (shift (-t) (neg_mem ht))
    (AlgHom.ext fun F => by
      have := shift_shift (-t) (neg_mem ht) F
      rw [shift_congr (neg_neg t) (neg_mem (neg_mem ht)) ht] at this
      exact this)
    (AlgHom.ext fun F => shift_shift t ht F)

theorem shiftEquiv_X : shiftEquiv t ht X = X + C t := by
  first
  | exact shift_X t ht
  | (show shift t ht X = X + C t; exact shift_X t ht)

theorem shiftEquiv_symm_X : (shiftEquiv t ht).symm X = X - C t := by
  first
  | (show shift (-t) (neg_mem ht) X = X - C t
     rw [shift_X, _root_.map_neg, sub_eq_add_neg])
  | (rw [AlgEquiv.symm_apply_eq, _root_.map_sub, shiftEquiv_X,
      show shiftEquiv t ht (C t) = C t from algC (shiftEquiv t ht).toAlgHom t]
     ring)

end Shift

end Formalism.MainNotions.N.FrobeniusPowerSeries.PB
