import Mathlib

namespace Formalism.L2.Col

open Matrix

variable (R : Type) [CommRing R] {n : ℕ}

def pM (s : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => if i = s j then 1 else 0

theorem pM_apply (s : Equiv.Perm (Fin n)) (i j : Fin n) : pM R s i j = if i = s j then 1 else 0 := rfl

theorem pM_one : pM R (1 : Equiv.Perm (Fin n)) = 1 := by
  ext i j
  rw [pM_apply, Matrix.one_apply, Equiv.Perm.one_apply]

theorem pM_mul (s t : Equiv.Perm (Fin n)) : pM R (s * t) = pM R s * pM R t := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (t j)]
  · rw [pM_apply, pM_apply, pM_apply, if_pos rfl, mul_one, Equiv.Perm.mul_apply]
  · intro b _ hb
    rw [pM_apply R t, if_neg hb, mul_zero]
  · simp

theorem pM_transpose (s : Equiv.Perm (Fin n)) : (pM R s)ᵀ = pM R s⁻¹ := by
  ext i j
  simp only [Matrix.transpose_apply, pM_apply]
  by_cases h : j = s i
  · rw [if_pos h, if_pos (by rw [h]; simp)]
  · rw [if_neg h, if_neg (fun h' => h (by rw [h']; simp))]

theorem pM_map {S : Type} [CommRing S] (f : R →+* S) (s : Equiv.Perm (Fin n)) : (pM R s).map f = pM S s := by
  ext i j
  simp only [Matrix.map_apply, pM_apply]
  split_ifs <;> simp

def permGL : Equiv.Perm (Fin n) →* GL (Fin n) R where
  toFun s := ⟨pM R s, pM R s⁻¹, by rw [← pM_mul, mul_inv_cancel, pM_one], by rw [← pM_mul, inv_mul_cancel, pM_one]⟩
  map_one' := Units.ext (pM_one R)
  map_mul' s t := Units.ext (pM_mul R s t)

theorem permGL_val (s : Equiv.Perm (Fin n)) : ((permGL R s : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = pM R s := rfl

end Formalism.L2.Col
