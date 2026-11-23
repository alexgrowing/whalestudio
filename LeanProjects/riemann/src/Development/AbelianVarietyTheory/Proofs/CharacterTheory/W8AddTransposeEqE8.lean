import Mathlib

open Matrix Polynomial
open scoped BigOperators

namespace GlobalTheory

def E8 : Matrix (Fin 8) (Fin 8) ℤ := CartanMatrix.E₈

def W8 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  1,  0, -1,  0,  0,  0,  0,  0;
       0,  1,  0, -1,  0,  0,  0,  0;
       0,  0,  1, -1,  0,  0,  0,  0;
       0,  0,  0,  1, -1,  0,  0,  0;
       0,  0,  0,  0,  1, -1,  0,  0;
       0,  0,  0,  0,  0,  1, -1,  0;
       0,  0,  0,  0,  0,  0,  1, -1;
       0,  0,  0,  0,  0,  0,  0,  1]

def E8inv : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  4,  5,  7, 10,  8,  6,  4,  2;
       5,  8, 10, 15, 12,  9,  6,  3;
       7, 10, 14, 20, 16, 12,  8,  4;
      10, 15, 20, 30, 24, 18, 12,  6;
       8, 12, 16, 24, 20, 15, 10,  5;
       6,  9, 12, 18, 15, 12,  8,  4;
       4,  6,  8, 12, 10,  8,  6,  3;
       2,  3,  4,  6,  5,  4,  3,  2]

def w8 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  4,  5,  3, -2, -2, -2, -2, -2;
       5,  8,  5, -3, -3, -3, -3, -3;
       7, 10,  7, -4, -4, -4, -4, -4;
      10, 15, 10, -5, -6, -6, -6, -6;
       8, 12,  8, -4, -4, -5, -5, -5;
       6,  9,  6, -3, -3, -3, -4, -4;
       4,  6,  4, -2, -2, -2, -2, -3;
       2,  3,  2, -1, -1, -1, -1, -1]

def E8roots : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  1,  2, -2,  0,  0,  0,  0,  0;
      -1,  2,  2, -2,  0,  0,  0,  0;
      -1,  0,  0,  2, -2,  0,  0,  0;
      -1,  0,  0,  0,  2, -2,  0,  0;
      -1,  0,  0,  0,  0,  2, -2,  0;
      -1,  0,  0,  0,  0,  0,  2, -2;
      -1,  0,  0,  0,  0,  0,  0,  2;
       1,  0,  0,  0,  0,  0,  0,  0]

theorem w8_add_transpose_eq_e8 : W8 + W8ᵀ = E8 := by decide

theorem e8_transpose : E8ᵀ = E8 := CartanMatrix.E₈_transpose

theorem e8_det_eq_one : E8.det = 1 := CartanMatrix.E₈_det

theorem e8inv_mul_e8 : E8inv * E8 = 1 := by decide

theorem e8_mul_e8inv : E8 * E8inv = 1 := by decide

theorem E8roots_transpose_mul_self : E8rootsᵀ * E8roots = (4 : ℤ) • E8 := by decide

theorem e8_posDef : (E8.map (fun x : ℤ => (x : ℝ))).PosDef := by
  set f : ℤ →+* ℝ := Int.castRingHom ℝ with hf
  change (E8.map f).PosDef
  have h : E8.map f = ((1 / 2 : ℝ) • E8roots.map f)ᴴ * ((1 / 2 : ℝ) • E8roots.map f) := by
    have h4 : (E8roots.map f)ᵀ * E8roots.map f = (4 : ℝ) • E8.map f := by
      rw [← Matrix.transpose_map, ← Matrix.map_mul, E8roots_transpose_mul_self]
      ext i j
      rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
        smul_eq_mul, map_mul]
      simp [hf]
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, h4, smul_smul, smul_smul]
    norm_num
  have hs : (E8.map f).PosSemidef := by
    rw [h]; exact Matrix.posSemidef_conjTranspose_mul_self _
  rw [hs.posDef_iff_det_ne_zero]
  have : (E8.map f).det = f E8.det := (RingHom.map_det f E8).symm
  rw [this, e8_det_eq_one, map_one]
  exact one_ne_zero

end GlobalTheory
