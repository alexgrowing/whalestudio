import Mathlib

open MvPolynomial

namespace Bl.general_b_fact_right

theorem goal1 {V ι : Type*} [AddCommGroup V] [Module ℂ V] (L : List ι) (F : ι → Module.End ℂ V)
    (c : ι → ℂ) (x : V) (hL : ∀ j ∈ L, F j x = c j • x) : (L.map F).prod x = (L.map c).prod • x := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have h1 : ∀ j ∈ L, F j x = c j • x := fun j hj => hL j (List.mem_cons_of_mem a hj)
    have h2 : F a x = c a • x := hL a (by simp)
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [ih h1, map_smul, h2, smul_smul, mul_comm]

end Bl.general_b_fact_right
