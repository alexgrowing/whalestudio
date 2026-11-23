import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqExpOfRat

noncomputable section

namespace GlobalTheory.Glue.Roots

open GlobalTheory.KZ GlobalTheory.K5

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem eOm_pow (ε : Ω →+* ℂ) (x : ℚ) (n : ℕ) : eOm ε x ^ n = eOm ε (n * x) := by
  apply ε.injective
  rw [map_pow, eOm_spec ε ε.injective, eOm_spec ε ε.injective, ← Complex.exp_nat_mul]
  congr 1; push_cast; ring

theorem isPrimitiveRoot_eOm_inv (ε : Ω →+* ℂ) {n : ℕ} (hn : n ≠ 0) :
    IsPrimitiveRoot (eOm ε (1 / (n : ℚ))) n := by
  apply IsPrimitiveRoot.of_map_of_injective (f := ε) _ ε.injective
  rw [eOm_spec ε ε.injective]
  convert Complex.isPrimitiveRoot_exp n hn using 2
  push_cast; ring

theorem isPrimitiveRoot_zt (ε : Ω →+* ℂ) {l : ℕ} (hl : l ≠ 0) (m : ℕ) :
    IsPrimitiveRoot (zt ε l m) (l ^ m) := by
  have h := isPrimitiveRoot_eOm_inv ε (pow_ne_zero m hl)
  rwa [Nat.cast_pow] at h

theorem zt_add_pow (ε : Ω →+* ℂ) {l : ℕ} (hl : l ≠ 0) (m k : ℕ) :
    zt ε l (m + k) ^ l ^ k = zt ε l m := by
  have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl
  rw [zt, zt, eOm_pow]
  congr 1; push_cast; field_simp; ring

theorem zt_succ_pow (ε : Ω →+* ℂ) {l : ℕ} (hl : l ≠ 0) (m : ℕ) :
    zt ε l (m + 1) ^ l = zt ε l m := by
  simpa using zt_add_pow ε hl m 1

theorem eOm_level_pow (ε : Ω →+* ℂ) {N : ℕ} (hN : N ≠ 0) (l m : ℕ) :
    eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ N = zt ε l m := by
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  rw [zt, eOm_pow]
  congr 1
  rw [one_div, one_div, mul_inv, ← mul_assoc, mul_inv_cancel₀ hN', one_mul]

theorem isPrimitiveRoot_eOm_level (ε : Ω →+* ℂ) {N l : ℕ} (hN : N ≠ 0) (hl : l ≠ 0) (m : ℕ) :
    IsPrimitiveRoot (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m))) (N * l ^ m) := by
  have h := isPrimitiveRoot_eOm_inv ε (mul_ne_zero hN (pow_ne_zero m hl))
  rwa [Nat.cast_mul, Nat.cast_pow] at h

theorem eOm_isPrimitiveRoot_compatible : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), Function.Injective ε →
    ∀ (l : ℕ), l.Prime → ∀ (N : ℕ), 0 < N → ∀ m : ℕ,
    IsPrimitiveRoot (eOm ε (1 / (l : ℚ) ^ m)) (l ^ m) ∧ eOm ε (1 / (l : ℚ) ^ (m + 1)) ^ l = eOm ε (1 / (l : ℚ) ^ m) ∧
    IsPrimitiveRoot (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m))) (N * l ^ m) ∧
    eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ N = eOm ε (1 / (l : ℚ) ^ m) := by
  intro Ω _ _ _ ε _ l hl N hN m
  have hl0 : l ≠ 0 := hl.ne_zero
  have hN0 : N ≠ 0 := hN.ne'
  exact ⟨isPrimitiveRoot_zt ε hl0 m, zt_succ_pow ε hl0 m, isPrimitiveRoot_eOm_level ε hN0 hl0 m, eOm_level_pow ε hN0 l m⟩

end GlobalTheory.Glue.Roots
