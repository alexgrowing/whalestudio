import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.HeckeOperator

open NumberField IsDedekindDomain Matrix CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

set_option linter.unusedSectionVars false

def triHecke (x z : ℕ) [NeZero x] [NeZero z] (c : ℤ) : GL (Fin 2) ℚ where
  val := !![(x : ℚ), -c; 0, z]
  inv := !![(x : ℚ)⁻¹, c / (x * z); 0, (z : ℚ)⁻¹]
  val_inv := by
    have hx := natCast_ne_zero_rat x
    have hz := natCast_ne_zero_rat z
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  inv_val := by
    have hx := natCast_ne_zero_rat x
    have hz := natCast_ne_zero_rat z
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

variable (p q : ℕ) [NeZero p] [NeZero q]

instance : NeZero (p * q) := ⟨Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne q)⟩

variable [Fact p.Prime]

variable [Fact q.Prime] (N : ℕ) [NeZero N]

variable {k : ℤ}

end GL2Classical

end

end GroundTheory.Automorphic
