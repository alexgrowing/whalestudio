import Mathlib

noncomputable section
open scoped BigOperators Matrix

namespace PI.KerFourSqW

def quatMat (r₁ r₂ r₃ r₄ : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![r₁, -r₂, -r₃, -r₄;
     r₂, r₁, -r₄, r₃;
     r₃, r₄, r₁, -r₂;
     r₄, -r₃, r₂, r₁]

theorem quatMat_transpose_mul (r₁ r₂ r₃ r₄ : ℚ) :
    (quatMat r₁ r₂ r₃ r₄)ᵀ * quatMat r₁ r₂ r₃ r₄ = (r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2 + r₄ ^ 2) • (1 : Matrix (Fin 4) (Fin 4) ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> ring

theorem rat_sum_four_squares (a : ℚ) (ha : 0 < a) :
    ∃ r₁ r₂ r₃ r₄ : ℚ, r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2 + r₄ ^ 2 = a := by
  obtain ⟨s₁, s₂, s₃, s₄, hs⟩ := Nat.sum_four_squares (a.num.toNat * a.den)
  have hnum : 0 < a.num := Rat.num_pos.mpr ha
  have hden : (0 : ℚ) < a.den := by exact_mod_cast a.pos
  refine ⟨s₁ / a.den, s₂ / a.den, s₃ / a.den, s₄ / a.den, ?_⟩
  have hcast : ((a.num.toNat * a.den : ℕ) : ℚ) = (a.num : ℚ) * a.den := by
    push_cast
    congr 1
    exact_mod_cast Int.toNat_of_nonneg hnum.le
  have h1 : ((s₁ : ℚ) ^ 2 + (s₂ : ℚ) ^ 2 + (s₃ : ℚ) ^ 2 + (s₄ : ℚ) ^ 2) = (a.num : ℚ) * a.den := by
    rw [← hcast]; exact_mod_cast hs
  rw [div_pow, div_pow, div_pow, div_pow, ← add_div, ← add_div, ← add_div, h1, pow_two, ← div_div,
    mul_div_cancel_right₀ _ hden.ne', Rat.num_div_den]

theorem exists_quat (a : ℚ) (ha : 0 < a) :
    ∃ Q : Matrix (Fin 4) (Fin 4) ℚ, Qᵀ * Q = a • (1 : Matrix (Fin 4) (Fin 4) ℚ) := by
  obtain ⟨r₁, r₂, r₃, r₄, h⟩ := rat_sum_four_squares a ha
  exact ⟨quatMat r₁ r₂ r₃ r₄, by rw [quatMat_transpose_mul, h]⟩

theorem sum_mul_cast {L : Type*} [Field L] [CharZero L] (Q : Matrix (Fin 4) (Fin 4) ℚ) (a : ℚ)
    (hQ : Qᵀ * Q = a • (1 : Matrix (Fin 4) (Fin 4) ℚ)) (j k : Fin 4) :
    ∑ b, (Q b j : L) * (Q b k : L) = if j = k then (a : L) else 0 := by
  have h := congrFun (congrFun hQ j) k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul] at h
  have h' : ((∑ b, Q b j * Q b k : ℚ) : L) = ((a * if j = k then 1 else 0 : ℚ) : L) := by rw [h]
  push_cast at h'
  rw [h']
  split_ifs <;> simp

theorem quat_herm {L F : Type*} [Field L] [CharZero L] [FunLike F L L] [RingHomClass F L L] (c : F) (Q : Matrix (Fin 4) (Fin 4) ℚ) (a : ℚ)
    (hQ : Qᵀ * Q = a • (1 : Matrix (Fin 4) (Fin 4) ℚ)) (x y : Fin 4 → L) :
    ∑ b, (∑ j, (Q b j : L) * x j) * c (∑ k, (Q b k : L) * y k) = (a : L) * ∑ j, x j * c (y j) := by
  have hc : ∀ b, c (∑ k, (Q b k : L) * y k) = ∑ k, (Q b k : L) * c (y k) := by
    intro b
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_ratCast]
  simp_rw [hc, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  have : ∀ j, ∑ b, ∑ k, (Q b j : L) * x j * ((Q b k : L) * c (y k))
      = ∑ k, (∑ b, (Q b j : L) * (Q b k : L)) * (x j * c (y k)) := by
    intro j
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  simp_rw [this, sum_mul_cast Q a hQ, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.mul_sum]

end PI.KerFourSqW
