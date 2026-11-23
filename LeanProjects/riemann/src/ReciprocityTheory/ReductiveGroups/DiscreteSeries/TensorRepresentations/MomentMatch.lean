import Mathlib

noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS

theorem moment_poly {ι κ : Type*} [Fintype ι] [Fintype κ] (b : ι → ℂ) (u : ι → ℂ) (a : κ → ℂ)
    (r : κ → ℂ) (h : ∀ k : ℕ, ∑ i, u i * b i ^ k = ∑ s, r s * a s ^ k) (Q : ℂ[X]) :
    ∑ i, u i * Q.eval (b i) = ∑ s, r s * Q.eval (a s) := by
  simp only [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc ∑ i, u i * (Q.coeff k * b i ^ k) = Q.coeff k * ∑ i, u i * b i ^ k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = Q.coeff k * ∑ s, r s * a s ^ k := by rw [h k]
    _ = ∑ s, r s * (Q.coeff k * a s ^ k) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

theorem moment_fibre {ι κ : Type*} [Fintype ι] [Fintype κ] (b : ι → ℂ) (u : ι → ℂ) (a : κ → ℂ)
    (r : κ → ℂ) (h : ∀ k : ℕ, ∑ i, u i * b i ^ k = ∑ s, r s * a s ^ k) (p : ℂ) :
    ∑ i ∈ univ.filter (fun i => b i = p), u i = ∑ s ∈ univ.filter (fun s => a s = p), r s := by
  classical
  set S : Finset ℂ := (univ.image b ∪ univ.image a).erase p with hS
  have hne : (∏ s ∈ S, (p - s)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun s hs => sub_ne_zero.mpr (Finset.ne_of_mem_erase hs).symm
  let Q : ℂ[X] := C (∏ s ∈ S, (p - s))⁻¹ * ∏ s ∈ S, (X - C s)
  have hQ : ∀ x, x ∈ univ.image b ∪ univ.image a → Q.eval x = if x = p then 1 else 0 := by
    intro x hx
    simp only [Q, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    split_ifs with hxp
    · subst hxp
      exact inv_mul_cancel₀ hne
    · rw [Finset.prod_eq_zero (i := x) (Finset.mem_erase.mpr ⟨hxp, hx⟩) (sub_self x), mul_zero]
  have e := moment_poly b u a r h Q
  rw [Finset.sum_filter, Finset.sum_filter]
  calc ∑ i, (if b i = p then u i else 0) = ∑ i, u i * Q.eval (b i) :=
        Finset.sum_congr rfl fun i _ => by
          rw [hQ (b i) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))]
          split_ifs <;> simp
    _ = ∑ s, r s * Q.eval (a s) := e
    _ = _ := Finset.sum_congr rfl fun s _ => by
          rw [hQ (a s) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))]
          split_ifs <;> simp

variable {n : ℕ}

theorem moment_match {ι : Type*} [Fintype ι] (b : ι → ℂ) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (a : Fin n → ℂ)
    (ha : Function.Injective a) (r : Fin n → ℂ)
    (h : ∀ k : ℕ, ∑ i, (w i : ℂ) * b i ^ k = ∑ s, r s * a s ^ k) :
    (∀ i, ∃ s, b i = a s) ∧ ∀ s, r s = ∑ i ∈ univ.filter (fun i => b i = a s), (w i : ℂ) := by
  classical
  refine ⟨fun i => ?_, fun s => ?_⟩
  · by_contra hcon
    push_neg at hcon
    have e := moment_fibre b (fun i => (w i : ℂ)) a r h (b i)
    have e0 : univ.filter (fun s => a s = b i) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun t _ h' => hcon t h'.symm
    rw [e0, Finset.sum_empty] at e
    have hpos : 0 < ∑ j ∈ univ.filter (fun j => b j = b i), w j :=
      Finset.sum_pos (fun j _ => hw j) ⟨i, by simp⟩
    have e' : ((∑ j ∈ univ.filter (fun j => b j = b i), w j : ℝ) : ℂ) = 0 := by
      push_cast
      exact e
    exact hpos.ne' (by exact_mod_cast e')
  · have e := moment_fibre b (fun i => (w i : ℂ)) a r h (a s)
    have e1 : univ.filter (fun t => a t = a s) = {s} := by
      ext t
      simp [ha.eq_iff]
    rw [e1, Finset.sum_singleton] at e
    exact e.symm

end ReciprocityTheory.ChartRestriction.DS
