import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD.Loc

variable {k : Type} [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} {x : Fin (d + 1) → F}

theorem gen_mem (I : Finset (Fin (d + 1))) {i : Fin (d + 1)} (hi : i ∈ I) (j : Fin (d + 1)) :
    x j / x i ∈ rA k x I :=
  Algebra.subset_adjoin ⟨i, hi, j, rfl⟩

theorem rA_mono {I J : Finset (Fin (d + 1))} (h : I ⊆ J) : rA k x I ≤ rA k x J :=
  Algebra.adjoin_mono fun _ ⟨i, hi, j, e⟩ => ⟨i, h hi, j, e⟩

theorem prod_mem_single (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) :
    ∏ j ∈ I, x j / x i ∈ rA k x {i} :=
  Subalgebra.prod_mem _ fun j _ => gen_mem {i} (Finset.mem_singleton_self i) j

theorem gen_mul_prod_mem (hne : ∀ l, x l ≠ 0) (I : Finset (Fin (d + 1))) (i : Fin (d + 1))
    {i' : Fin (d + 1)} (hi' : i' ∈ I) (j : Fin (d + 1)) :
    x j / x i' * ∏ l ∈ I, x l / x i ∈ rA k x {i} := by
  rw [← Finset.mul_prod_erase I (fun l => x l / x i) hi', ← mul_assoc]
  have e : x j / x i' * (x i' / x i) = x j / x i := by
    field_simp [hne i', hne i]
  rw [e]
  exact Subalgebra.mul_mem _ (gen_mem {i} (Finset.mem_singleton_self i) j)
    (Subalgebra.prod_mem _ fun l _ => gen_mem {i} (Finset.mem_singleton_self i) l)

end GlobalTheory.PD.Loc

open GlobalTheory.PD.Loc in

theorem GlobalTheory.PD.rA_eq_loc : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F),
    IsPd k x → ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → ∀ y : F,
      y ∈ rA k x I ↔ ∃ N : ℕ, y * (∏ j ∈ I, x j / x i) ^ N ∈ rA k x {i} := by
  intro k _ F _ _ d x hx I i hi y
  set P := ∏ j ∈ I, x j / x i with hP
  have hPm : P ∈ rA k x {i} := prod_mem_single I i
  constructor
  · intro hy
    induction hy using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨i', hi', j, rfl⟩ := hz
      exact ⟨1, by rw [pow_one]; exact gen_mul_prod_mem hx.ne I i hi' j⟩
    | algebraMap r => exact ⟨0, by rw [pow_zero, mul_one]; exact Subalgebra.algebraMap_mem _ r⟩
    | add a b _ _ ha hb =>
      obtain ⟨N₁, h₁⟩ := ha
      obtain ⟨N₂, h₂⟩ := hb
      refine ⟨N₁ + N₂, ?_⟩
      have e : (a + b) * P ^ (N₁ + N₂) = (a * P ^ N₁) * P ^ N₂ + (b * P ^ N₂) * P ^ N₁ := by ring
      rw [e]
      exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ h₁ (Subalgebra.pow_mem _ hPm _))
        (Subalgebra.mul_mem _ h₂ (Subalgebra.pow_mem _ hPm _))
    | mul a b _ _ ha hb =>
      obtain ⟨N₁, h₁⟩ := ha
      obtain ⟨N₂, h₂⟩ := hb
      refine ⟨N₁ + N₂, ?_⟩
      have e : (a * b) * P ^ (N₁ + N₂) = (a * P ^ N₁) * (b * P ^ N₂) := by ring
      rw [e]
      exact Subalgebra.mul_mem _ h₁ h₂
  · rintro ⟨N, hN⟩
    have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => div_ne_zero (hx.ne j) (hx.ne i)
    have hPinv : P⁻¹ ∈ rA k x I := by
      rw [hP, ← Finset.prod_inv_distrib]
      exact Subalgebra.prod_mem _ fun j hj => by rw [inv_div]; exact gen_mem I hj i
    have e : y = (y * P ^ N) * P⁻¹ ^ N := by
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hP0, one_pow, mul_one]
    rw [e]
    exact Subalgebra.mul_mem _ (rA_mono (Finset.singleton_subset_iff.2 hi) hN) (Subalgebra.pow_mem _ hPinv _)
