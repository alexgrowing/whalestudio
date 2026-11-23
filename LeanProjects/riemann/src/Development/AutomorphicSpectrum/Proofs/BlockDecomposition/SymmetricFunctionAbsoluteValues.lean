import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic

open PositivityTheory.JacquetShalikaLocal GroundTheory.Automorphic GroundTheory.Automorphic.Spherical

namespace GlobalTheory.CompanionTheory.JSBound

theorem evalAt_esymmL_eq_sum_prod {n : ℕ} (z : Fin n → ℂˣ) (r : ℕ) :
    evalAt z (esymmL n r) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, (z i : ℂ) := by
  unfold esymmL
  rw [map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [evalAt, monomial, AddMonoidAlgebra.lift_single, one_smul, pointHom, monomialChar,
    MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, lamS]
  rw [← Fintype.prod_ite_mem S]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem prod_one_add_mul_eq {n : ℕ} (w : Fin n → ℂ) (t : ℂ) :
    ∏ j, (1 + t * w j) = ∑ r ∈ Finset.range (n + 1),
      t ^ r * ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, w i := by
  have h := Finset.prod_add (fun j => t * w j) (fun _ => (1 : ℂ)) (Finset.univ : Finset (Fin n))
  simp only [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const] at h
  rw [show (∏ j, (1 + t * w j)) = ∏ j, (t * w j + 1) from Finset.prod_congr rfl fun _ _ => add_comm _ _, h,
    Finset.sum_powerset, Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [(Finset.mem_powersetCard.1 hS).2]

theorem prod_add_eq {n : ℕ} (z : Fin n → ℂ) (t : ℂ) :
    ∏ j, (t + z j) = ∑ r ∈ Finset.range (n + 1),
      t ^ (n - r) * ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i := by
  rw [show (∏ j, (t + z j)) = ∏ j, (z j + t) from Finset.prod_congr rfl fun _ _ => add_comm _ _,
    Finset.prod_add, Finset.sum_powerset, Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.prod_const, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin,
    (Finset.mem_powersetCard.1 hS).2, mul_comm]

theorem mul_prod_one_add_conj_eq {n : ℕ} (z : Fin n → ℂˣ)
    (h : ∀ r ≤ n, starRingEnd ℂ (evalAt z (esymmL n r)) * evalAt z (esymmL n n) =
      evalAt z (esymmL n (n - r))) (t : ℂ) :
    evalAt z (esymmL n n) * ∏ j, (1 + t * starRingEnd ℂ (z j : ℂ)) = ∏ j, (t + (z j : ℂ)) := by
  simp only [evalAt_esymmL_eq_sum_prod] at h ⊢
  rw [prod_one_add_mul_eq, prod_add_eq, Finset.mul_sum]
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrn : r ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  have key := h r hrn
  simp only [map_sum, map_prod] at key
  rw [Nat.add_sub_cancel, Nat.sub_sub_self hrn, ← key]
  ring

theorem symmetric_function_absolute_values : ParameterAbsoluteValues := by
  unfold ParameterAbsoluteValues
  intro n z h i
  have h0 := mul_prod_one_add_conj_eq z h 0
  have h1 := mul_prod_one_add_conj_eq z h (-(z i : ℂ))
  simp only [zero_mul, add_zero, zero_add, Finset.prod_const_one, mul_one] at h0
  have hne : evalAt z (esymmL n n) ≠ 0 := by
    rw [h0]
    exact Finset.prod_ne_zero_iff.2 fun j _ => (z j).ne_zero
  have hz : ∏ j, (-(z i : ℂ) + z j) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by ring)
  rw [hz, mul_eq_zero] at h1
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 (h1.resolve_left hne)
  refine ⟨j, ?_⟩
  have hc : (z i : ℂ) * starRingEnd ℂ (z j : ℂ) = 1 := by linear_combination -hj
  have hn := congrArg norm hc
  rw [norm_mul, Complex.norm_conj, norm_one] at hn
  rw [mul_comm]
  exact hn

end GlobalTheory.CompanionTheory.JSBound
