import Mathlib

open Matrix

namespace GlobalTheory

def killersEquiv {k : Type} [Field k] {m n : ℕ} (A : Matrix (Fin n) (Fin n) k) :
    {w : Matrix (Fin m) (Fin n) k // w * A = 0} ≃ (Fin m → LinearMap.ker (Aᵀ).mulVecLin) where
  toFun w i := ⟨w.1 i, by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose]
    funext l
    have := congrFun (congrFun w.2 i) l
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct] using this⟩
  invFun f := ⟨Matrix.of fun i => (f i).1, by
    ext i l
    have h := (f i).2
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose] at h
    have := congrFun h l
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct] using this⟩
  left_inv w := by ext i l; rfl
  right_inv f := by ext i l; rfl

theorem natCard_matrices_mul_eq_zero (k : Type) [Field k] [Finite k] (m n j : ℕ)
    (A : Matrix (Fin n) (Fin n) k)
    (h : Module.finrank k (LinearMap.range A.mulVecLin) + j = n) :
    Nat.card {w : Matrix (Fin m) (Fin n) k // w * A = 0} = Nat.card k ^ (j * m) := by
  have h1 : Module.finrank k (LinearMap.range (Aᵀ).mulVecLin)
      = Module.finrank k (LinearMap.range A.mulVecLin) := Matrix.rank_transpose A
  have h2 := LinearMap.finrank_range_add_finrank_ker (Aᵀ).mulVecLin
  rw [h1, Module.finrank_fin_fun] at h2
  have h3 : Module.finrank k (LinearMap.ker (Aᵀ).mulVecLin) = j := by omega
  rw [Nat.card_congr (killersEquiv A), Nat.card_fun, Module.natCard_eq_pow_finrank (K := k), h3,
    Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin, pow_mul]

end GlobalTheory
