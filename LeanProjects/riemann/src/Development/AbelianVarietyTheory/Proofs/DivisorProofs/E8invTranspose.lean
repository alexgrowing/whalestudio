import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8

noncomputable section

namespace GlobalTheory.Mum.E8Ring

open Matrix

theorem E8inv_transpose : GlobalTheory.E8invᵀ = GlobalTheory.E8inv := by decide

def O8 : Type := Matrix (Fin 8) (Fin 8) ℤ

instance : Ring O8 := inferInstanceAs (Ring (Matrix (Fin 8) (Fin 8) ℤ))

def adj (a : Matrix (Fin 8) (Fin 8) ℤ) : Matrix (Fin 8) (Fin 8) ℤ := GlobalTheory.E8inv * aᵀ * GlobalTheory.E8

theorem adj_adj (a : Matrix (Fin 8) (Fin 8) ℤ) : adj (adj a) = a := by
  unfold adj
  rw [transpose_mul, transpose_mul, transpose_transpose, GlobalTheory.e8_transpose, E8inv_transpose]
  simp only [Matrix.mul_assoc]
  rw [GlobalTheory.e8inv_mul_e8, Matrix.mul_one, ← Matrix.mul_assoc, GlobalTheory.e8inv_mul_e8, Matrix.one_mul]

theorem adj_mul (a b : Matrix (Fin 8) (Fin 8) ℤ) : adj (a * b) = adj b * adj a := by
  unfold adj
  rw [transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc GlobalTheory.E8 GlobalTheory.E8inv, GlobalTheory.e8_mul_e8inv, Matrix.one_mul]

theorem adj_add (a b : Matrix (Fin 8) (Fin 8) ℤ) : adj (a + b) = adj a + adj b := by
  unfold adj
  rw [transpose_add, Matrix.mul_add, Matrix.add_mul]

instance : StarRing O8 where
  star a := adj a
  star_involutive a := adj_adj a
  star_mul a b := adj_mul a b
  star_add a b := adj_add a b

def e8 : O8 := Matrix.single (0 : Fin 8) (0 : Fin 8) (1 : ℤ)

def f8 : O8 := -Matrix.single (2 : Fin 8) (0 : Fin 8) (1 : ℤ)

end GlobalTheory.Mum.E8Ring
