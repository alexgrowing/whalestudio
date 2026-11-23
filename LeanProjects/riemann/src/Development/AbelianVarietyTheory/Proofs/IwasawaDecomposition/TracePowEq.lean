import Mathlib

namespace GlobalTheory.TracePowEq

open Matrix

theorem trace_pow_eq {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ}
    (E : Fin n → Fin n → A) (E' : Fin m → Fin m → A)
    (P : Matrix (Fin m) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin m) ℂ)
    (hPQ : P * Q = (1 : Matrix (Fin m) (Fin m) ℂ))
    (hQP : Q * P = (1 : Matrix (Fin n) (Fin n) ℂ))
    (h : ∀ (a b : Fin m), E' a b = ∑ c : Fin n, ∑ d : Fin n, (Q c a * P b d) • E c d) (k : ℕ) :
    ∑ c : Fin m, ((Matrix.of : (Fin m → Fin m → A) → Matrix (Fin m) (Fin m) A) E' ^ k) c c
      = ∑ c : Fin n, ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ k) c c := by

  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin m) (Fin n) A, S = Qᵀ.map (algebraMap ℂ A) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin m) A, T = Pᵀ.map (algebraMap ℂ A) := ⟨_, rfl⟩
  have hTS : T * S = 1 := by
    rw [hT, hS, ← Matrix.map_mul, ← Matrix.transpose_mul, hQP, Matrix.transpose_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hST : S * T = 1 := by
    rw [hT, hS, ← Matrix.map_mul, ← Matrix.transpose_mul, hPQ, Matrix.transpose_one,
      Matrix.map_one _ (map_zero _) (map_one _)]

  have hE : (Matrix.of E' : Matrix (Fin m) (Fin m) A) = S * Matrix.of E * T := by
    ext a b
    have key : ∀ c d, (Q c a * P b d) • E c d = S a c * E c d * T d b := by
      intro c d
      rw [hS, hT, Matrix.map_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.transpose_apply,
        Algebra.smul_def, map_mul, mul_assoc, Algebra.commutes (P b d) (E c d), ← mul_assoc]
    rw [Matrix.of_apply, h a b]
    simp only [key, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
    exact Finset.sum_comm

  have hpow : ∀ j : ℕ, (S * Matrix.of E * T) ^ j = S * Matrix.of E ^ j * T := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hST]
    | succ j ih =>
      rw [pow_succ, ih, pow_succ]
      calc S * Matrix.of E ^ j * T * (S * Matrix.of E * T)
          = S * Matrix.of E ^ j * (T * S) * Matrix.of E * T := by simp only [Matrix.mul_assoc]
        _ = S * (Matrix.of E ^ j * Matrix.of E) * T := by rw [hTS, Matrix.mul_one, Matrix.mul_assoc S]

  have hcyc : ∀ X : Matrix (Fin n) (Fin m) A, ∑ c, (S * X) c c = ∑ d, (X * S) d d := by
    intro X
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ => ?_
    rw [hS, Matrix.map_apply, Algebra.commutes]
  rw [hE, hpow, Matrix.mul_assoc, hcyc, Matrix.mul_assoc, hTS, Matrix.mul_one]

end GlobalTheory.TracePowEq
