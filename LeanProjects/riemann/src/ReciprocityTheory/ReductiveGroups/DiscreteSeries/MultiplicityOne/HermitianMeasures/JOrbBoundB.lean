import Formalism.HermitianCurvature.WeylElementCommutesLevelOne

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section Form

variable {k r : ℕ}

def sigI (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩

def sgnI (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

end Form

section Level

variable {k r' : ℕ}

def i0 (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := ⟨0, by omega⟩

def iL (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := ⟨2 * (1 + r') + k, by omega⟩

def iM (k r' : ℕ) (j : Fin (2 * r' + k + 1)) : Fin (2 * (1 + r') + k + 1) := ⟨j.val + 1, by omega⟩

def mid (k r' : ℕ) (v : Fin (2 * (1 + r') + k + 1) → ℂ) : Fin (2 * r' + k + 1) → ℂ := fun j => v (iM k r' j)

@[simp] theorem first_index_val : (i0 k r').val = 0 := rfl
@[simp] theorem iL_val : (iL k r').val = 2 * (1 + r') + k := rfl
@[simp] theorem iM_val (j : Fin (2 * r' + k + 1)) : (iM k r' j).val = j.val + 1 := rfl

@[simp] theorem middle_ne_first_index (j : Fin (2 * r' + k + 1)) : iM k r' j ≠ i0 k r' := by
  rw [Ne, Fin.ext_iff, iM_val, first_index_val]; omega
@[simp] theorem first_ne_middle_index (j : Fin (2 * r' + k + 1)) : i0 k r' ≠ iM k r' j := fun h => middle_ne_first_index j h.symm
@[simp] theorem iM_ne_iL (j : Fin (2 * r' + k + 1)) : iM k r' j ≠ iL k r' := by
  have := j.isLt; rw [Ne, Fin.ext_iff, iM_val, iL_val]; omega
@[simp] theorem iL_ne_iM (j : Fin (2 * r' + k + 1)) : iL k r' ≠ iM k r' j := fun h => iM_ne_iL j h.symm
@[simp] theorem first_ne_last_index : i0 k r' ≠ iL k r' := by rw [Ne, Fin.ext_iff, first_index_val, iL_val]; omega
@[simp] theorem last_ne_first_index : iL k r' ≠ i0 k r' := fun h => first_ne_last_index h.symm
@[simp] theorem iM_inj {a b : Fin (2 * r' + k + 1)} : iM k r' a = iM k r' b ↔ a = b := by
  rw [Fin.ext_iff, Fin.ext_iff, iM_val, iM_val]; constructor <;> intro h <;> omega

theorem lift_apply (y : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1)) : liftVec k 1 r' y p =
    if hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 then y ⟨p.val - 1, by omega⟩ else 0 := rfl

@[simp] theorem lifted_vector_first (y : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' y (i0 k r') = 0 := by
  rw [lift_apply, dif_neg (by simp)]

@[simp] theorem lift_iL (y : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' y (iL k r') = 0 := by
  rw [lift_apply, dif_neg (by simp only [iL_val]; omega)]

@[simp] theorem lift_iM (y : Fin (2 * r' + k + 1) → ℂ) (j : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' y (iM k r' j) = y j := by
  have := j.isLt
  rw [lift_apply, dif_pos (by simp only [iM_val]; omega)]
  exact congrArg y (Fin.ext (by simp))

end Level

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB
