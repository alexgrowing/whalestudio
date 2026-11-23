import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

set_option autoImplicit false

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

open Polynomial in

theorem coeff_max_mul_linear {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ)
    (p : F[X]) (N : Γ) (α β : F) (h1 : ∀ i, v (p.coeff i) ≤ N) (h2 : ∃ i, v (p.coeff i) = N) :
    (∀ i, v (((C α + C β * X) * p).coeff i) ≤ max (v α) (v β) * N) ∧
      ∃ i, v (((C α + C β * X) * p).coeff i) = max (v α) (v β) * N := by
  classical
  have c0 : ((C α + C β * X) * p).coeff 0 = α * p.coeff 0 := by
    simp [add_mul, mul_assoc]
  have cs : ∀ i, ((C α + C β * X) * p).coeff (i + 1) = α * p.coeff (i + 1) + β * p.coeff i := by
    intro i
    simp [add_mul, mul_assoc, coeff_X_mul]
  have hle : ∀ i, v (((C α + C β * X) * p).coeff i) ≤ max (v α) (v β) * N := by
    intro i
    cases i with
    | zero =>
      rw [c0, map_mul]
      exact mul_le_mul' (le_max_left _ _) (h1 _)
    | succ i =>
      rw [cs]
      refine v.map_add_le ?_ ?_
      · rw [map_mul]; exact mul_le_mul' (le_max_left _ _) (h1 _)
      · rw [map_mul]; exact mul_le_mul' (le_max_right _ _) (h1 _)
  refine ⟨hle, ?_⟩
  by_cases hz : max (v α) (v β) * N = 0
  · exact ⟨0, le_antisymm (hle 0) (hz ▸ zero_le')⟩
  have hM : max (v α) (v β) ≠ 0 := left_ne_zero_of_mul hz
  have hN : N ≠ 0 := right_ne_zero_of_mul hz
  rcases le_or_gt (v β) (v α) with h | h
  · rw [max_eq_left h] at hM ⊢
    have hs := Nat.find_spec h2
    have hm := fun j => @Nat.find_min _ _ h2 j
    refine ⟨Nat.find h2, ?_⟩
    generalize Nat.find h2 = i at hs hm
    cases i with
    | zero => rw [c0, map_mul, hs]
    | succ i =>
      have hlt : v (p.coeff i) < N := lt_of_le_of_ne (h1 i) (hm i (Nat.lt_succ_self i))
      rw [cs, v.map_add_eq_of_lt_left, map_mul, hs]
      rw [map_mul, map_mul, hs]
      calc v β * v (p.coeff i) ≤ v α * v (p.coeff i) := mul_le_mul' h le_rfl
        _ < v α * N := mul_lt_mul_of_pos_left hlt (zero_lt_iff.2 hM)
  · rw [max_eq_right h.le]
    obtain ⟨i, hi⟩ := h2
    refine ⟨i + 1, ?_⟩
    rw [cs, v.map_add_eq_of_lt_right, map_mul, hi]
    rw [map_mul, map_mul, hi]
    calc v α * v (p.coeff (i + 1)) ≤ v α * N := mul_le_mul' le_rfl (h1 _)
      _ < v β * N := mul_lt_mul_of_pos_right h (zero_lt_iff.2 hN)

open Polynomial in

theorem coeff_max_prod_linear {F Γ ι : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ)
    (α β : ι → F) (s : Finset ι) :
    (∀ i, v ((∏ j ∈ s, (C (α j) + C (β j) * X)).coeff i) ≤ ∏ j ∈ s, max (v (α j)) (v (β j))) ∧
      ∃ i, v ((∏ j ∈ s, (C (α j) + C (β j) * X)).coeff i) = ∏ j ∈ s, max (v (α j)) (v (β j)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun i => ?_, 0, by simp⟩
    by_cases h : i = 0 <;> simp [coeff_one, h]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact coeff_max_mul_linear v _ _ _ _ ih.1 ih.2

theorem nrm_coeff_prod_linear : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], ∀ (v : Place k F) (m : ℕ) (α β : Fin m → F), nrm v (fun a : Fin (m + 1) => (∏ j, (Polynomial.C (α j) + Polynomial.C (β j) * Polynomial.X)).coeff a) = ∏ j, max (v.1 (α j)) (v.1 (β j)) := by
  intro k F _ _ _ v m α β
  obtain ⟨h1, i, hi⟩ := coeff_max_prod_linear v.1 α β Finset.univ
  have hdeg : (∏ j, (Polynomial.C (α j) + Polynomial.C (β j) * Polynomial.X)).natDegree ≤ m := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc _ ≤ ∑ _j : Fin m, 1 := Finset.sum_le_sum fun j _ => by
            rw [add_comm]; exact Polynomial.natDegree_linear_le
      _ = m := by simp
  refine le_antisymm (Finset.sup_le fun a _ => h1 a) ?_
  rw [← hi]
  by_cases him : i < m + 1
  · exact Finset.le_sup (f := fun a : Fin (m + 1) =>
      v.1 ((∏ j, (Polynomial.C (α j) + Polynomial.C (β j) * Polynomial.X)).coeff a))
      (Finset.mem_univ (⟨i, him⟩ : Fin (m + 1)))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
    exact zero_le'

end GlobalTheory.Nef
