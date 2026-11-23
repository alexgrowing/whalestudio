import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest

open scoped Matrix
open Matrix

noncomputable section

namespace PositivityTheory.Rg.Sw.KAKB

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def S0 (n : ℕ) : M2 n := fromBlocks 1 0 0 (-1)

def C0 (n : ℕ) : M2 n := fromBlocks 1 1 (Complex.I • 1) (-(Complex.I • 1))

def C1 (n : ℕ) : M2 n := (1 / 2 : ℂ) • (C0 n)ᴴ

theorem cayley_conjTranspose_eq : (C0 n)ᴴ = fromBlocks 1 (-(Complex.I • 1)) 1 (Complex.I • 1) := by
  simp [C0, fromBlocks_conjTranspose, conjTranspose_smul]

theorem cayley_conjTranspose_mul : (C0 n)ᴴ * C0 n = (2 : ℂ) • 1 := by
  rw [cayley_conjTranspose_eq, C0, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul]
  congr 1 <;> simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, two_smul] <;> module

theorem cayley_mul_conjTranspose : C0 n * (C0 n)ᴴ = (2 : ℂ) • 1 := by
  rw [cayley_conjTranspose_eq, C0, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul]
  congr 1 <;> simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, two_smul] <;> module

theorem cayley_inverse_mul : C1 n * C0 n = 1 := by
  rw [C1, Matrix.smul_mul, cayley_conjTranspose_mul, smul_smul]; norm_num

theorem cayley_mul_inverse : C0 n * C1 n = 1 := by
  rw [C1, Matrix.mul_smul, cayley_mul_conjTranspose, smul_smul]; norm_num

theorem complex_structure_cayley : JJ n * C0 n = C0 n * (Complex.I • S0 n) := by
  simp only [JJ, C0, S0, fromBlocks_multiply, fromBlocks_smul]
  congr 1 <;> simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul] <;> module

end PositivityTheory.Rg.Sw.KAKB

end
