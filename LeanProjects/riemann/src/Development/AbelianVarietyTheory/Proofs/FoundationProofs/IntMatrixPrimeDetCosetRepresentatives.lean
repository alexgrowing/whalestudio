import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem exists_right_div_upperTriangular_prime_det (q : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (k : ℕ)
    (h1 : (q : ℤ) ∣ m 0 1 - m 0 0 * k) (h2 : (q : ℤ) ∣ m 1 1 - m 1 0 * k) :
    ∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![1, (k : ℤ); 0, (q : ℤ)] = m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨c, hc⟩ := h2
  refine ⟨!![m 0 0, a; m 1 0, c], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination -ha | linear_combination ha | linear_combination -hc

theorem cosetPrimeDet : ∀ (q : ℕ), q.Prime → ∀ m : Matrix (Fin 2) (Fin 2) ℤ, m.det = q →
    (∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![(q : ℤ), 0; 0, 1] = m) ∨
    ∃ k : ℕ, k < q ∧ ∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![1, (k : ℤ); 0, (q : ℤ)] = m := by
  intro q hq m hdet
  have := Fact.mk hq
  have : NeZero q := ⟨hq.ne_zero⟩
  rw [Matrix.det_fin_two] at hdet
  have hd : ((m 0 0 : ℤ) : ZMod q) * (m 1 1 : ℤ) - ((m 0 1 : ℤ) : ZMod q) * (m 1 0 : ℤ) = 0 := by
    have : ((m 0 0 * m 1 1 - m 0 1 * m 1 0 : ℤ) : ZMod q) = 0 := by
      rw [hdet]; simp
    push_cast at this
    exact this

  have dv : ∀ x : ℤ, (x : ZMod q) = 0 → (q : ℤ) ∣ x := fun x hx =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd x q).mp hx

  have fin : ∀ t : ZMod q, ((m 0 1 : ℤ) : ZMod q) - (m 0 0 : ℤ) * t = 0 →
      ((m 1 1 : ℤ) : ZMod q) - (m 1 0 : ℤ) * t = 0 →
      ∃ k : ℕ, k < q ∧ ∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![1, (k : ℤ); 0, (q : ℤ)] = m := by
    intro t ht1 ht2
    refine ⟨t.val, ZMod.val_lt t, exists_right_div_upperTriangular_prime_det q m t.val (dv _ ?_) (dv _ ?_)⟩
    · push_cast; rw [ZMod.natCast_zmod_val]; exact ht1
    · push_cast; rw [ZMod.natCast_zmod_val]; exact ht2
  by_cases ha : ((m 0 0 : ℤ) : ZMod q) = 0
  · by_cases hc : ((m 1 0 : ℤ) : ZMod q) = 0
    ·
      left
      obtain ⟨x, hx⟩ := dv _ ha
      obtain ⟨y, hy⟩ := dv _ hc
      refine ⟨!![x, m 0 1; y, m 1 1], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | linear_combination -hx | linear_combination hx | linear_combination -hy
    · right
      have h01 : ((m 0 1 : ℤ) : ZMod q) = 0 := by
        have : ((m 0 1 : ℤ) : ZMod q) * (m 1 0 : ℤ) = 0 := by
          linear_combination -hd + ((m 1 1 : ℤ) : ZMod q) * ha
        exact (mul_eq_zero.mp this).resolve_right hc
      have hinv := mul_inv_cancel₀ hc
      refine fin (((m 1 1 : ℤ) : ZMod q) * ((m 1 0 : ℤ) : ZMod q)⁻¹) ?_ ?_
      · rw [ha, h01]; ring
      · linear_combination -((m 1 1 : ℤ) : ZMod q) * hinv
  · right
    have hinv := mul_inv_cancel₀ ha
    refine fin (((m 0 1 : ℤ) : ZMod q) * ((m 0 0 : ℤ) : ZMod q)⁻¹) ?_ ?_
    · linear_combination -((m 0 1 : ℤ) : ZMod q) * hinv
    · linear_combination ((m 0 0 : ℤ) : ZMod q)⁻¹ * hd - ((m 1 1 : ℤ) : ZMod q) * hinv

end GlobalTheory
