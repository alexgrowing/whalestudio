import Mathlib

namespace GlobalTheory.LagrangeInterpolationExistence

theorem exists_sum_add {X M : Type} [AddCommGroup M] [Module ℂ M] (S : Finset X) (a : X → M)
    (y : X) (b : M) :
    ∃ (T : Finset X) (u : X → M), ∀ c : X → ℂ,
      ∑ x ∈ T, c x • u x = ∑ x ∈ S, c x • a x + c y • b := by
  classical
  refine ⟨insert y S, fun x => if x = y then (if y ∈ S then a y + b else b) else a x, fun c => ?_⟩
  by_cases hy : y ∈ S
  · rw [Finset.insert_eq_of_mem hy, ← Finset.add_sum_erase S _ hy, ← Finset.add_sum_erase S _ hy]
    simp only [if_pos rfl, hy, if_true, ite_true, smul_add]
    rw [Finset.sum_congr rfl (fun x hx => by rw [if_neg (Finset.ne_of_mem_erase hx)])]
    abel
  · rw [Finset.sum_insert hy]
    simp only [if_neg hy, eq_self_iff_true, if_true, ite_true]
    rw [Finset.sum_congr rfl (fun x hx => by rw [if_neg (fun (h : x = y) => hy (h ▸ hx))]), add_comm]

theorem exists_interpolation {X : Type} (V : Submodule ℂ (X → ℂ)) (F : Finset V) :
    ∃ (S : Finset X) (u : X → V), ∀ f ∈ F, f = ∑ x ∈ S, (f : X → ℂ) x • u x := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨∅, 0, by simp⟩
  | insert g F _ ih =>
    obtain ⟨S, u, hu⟩ := ih
    set h : V := g - ∑ x ∈ S, (g : X → ℂ) x • u x with hh
    by_cases h0 : h = 0
    · refine ⟨S, u, fun f hf => ?_⟩
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact sub_eq_zero.mp h0
      · exact hu f hf
    · obtain ⟨y, hy⟩ : ∃ y, (h : X → ℂ) y ≠ 0 := by
        by_contra hc
        apply h0
        ext y
        by_contra hy
        exact hc ⟨y, by simpa using hy⟩
      obtain ⟨T, w, hw⟩ := exists_sum_add S
        (fun x => u x - ((u x : X → ℂ) y / (h : X → ℂ) y) • h) y (((h : X → ℂ) y)⁻¹ • h)
      have key : ∀ f : V, ∑ x ∈ T, (f : X → ℂ) x • w x =
          ∑ x ∈ S, (f : X → ℂ) x • u x +
            (((f - ∑ x ∈ S, (f : X → ℂ) x • u x : V) : X → ℂ) y / (h : X → ℂ) y) • h := by
        intro f
        rw [hw]
        simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul,
          Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Pi.sub_apply,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_div, sub_smul, Finset.sum_div,
          mul_div_assoc, div_eq_mul_inv, Finset.sum_mul, mul_assoc, sub_mul]
        abel
      refine ⟨T, w, fun f hf => ?_⟩
      rw [key]
      rcases Finset.mem_insert.mp hf with rfl | hf
      · rw [← hh, div_self hy, one_smul, hh]; abel
      · rw [← hu f hf]; simp

end GlobalTheory.LagrangeInterpolationExistence
