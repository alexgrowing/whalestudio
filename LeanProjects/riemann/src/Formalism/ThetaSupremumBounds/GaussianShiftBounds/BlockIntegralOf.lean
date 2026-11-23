import Mathlib
import Formalism.LogFactorialBounds.LogFactorialSandwich
import Formalism.ThetaSupremumBounds.StatementA

open Finset MeasureTheory
open scoped ComplexConjugate Real

namespace Formalism.DimensionVariation

open Formalism.LatticeIndexTer (ph)

private theorem rpow_mul_exp_neg_sq_le_exp_ph_mul_exp_log (ν s a : ℝ) (hν : 0 ≤ ν) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hνa : ν = 0 ∨ 0 < a) :
    s ^ ν * Real.exp (-(a * s ^ 2) / 2) ≤ Real.exp (ph ν / 2) * Real.exp (-(ν * Real.log a) / 2) := by
  rcases hν.eq_or_lt with h0 | hν
  · subst h0
    have : Real.exp (-(a * s ^ 2) / 2) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg ha (sq_nonneg s)])
    simpa [ph] using this
  · have ha' : 0 < a := hνa.resolve_left hν.ne'
    rcases hs.eq_or_lt with hs0 | hs
    · subst hs0
      rw [Real.zero_rpow hν.ne', zero_mul]; positivity
    · rw [Real.rpow_def_of_pos hs, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have hy := Real.log_le_sub_one_of_pos (show 0 < a * s ^ 2 / ν by positivity)
      rw [Real.log_div (by positivity) hν.ne', Real.log_mul ha'.ne' (by positivity), Real.log_pow] at hy
      have h2 : ν * (a * s ^ 2 / ν - 1) = a * s ^ 2 - ν := by field_simp
      have h3 := mul_le_mul_of_nonneg_left hy hν.le
      rw [h2] at h3
      push_cast at h3
      unfold ph
      nlinarith

theorem placeBound (r : ℕ) (ν sv : Fin r → ℝ) (Q : ℝ) (hν : ∀ i, 0 ≤ ν i) (hs : ∀ i, 0 ≤ sv i)
    (hQ : ∑ i, sv i ^ 2 = Q) :
    (∏ i, sv i ^ ν i) * Real.exp (-Q / 2) ≤
      Real.exp (1 / 2) * Real.exp ((∑ i, ph (ν i)) / 2) *
        Real.exp (-(1 / ((∑ i, ν i) + 1)) * Q / 2) := by
  set N := ∑ i, ν i with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => hν i
  set a : ℝ := 1 - 1 / (N + 1) with ha
  have hinv : 1 / (N + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hsplit : (∏ i, sv i ^ ν i) * Real.exp (-Q / 2) =
      (∏ i, (sv i ^ ν i * Real.exp (-(a * sv i ^ 2) / 2))) * Real.exp (-(1 / (N + 1)) * Q / 2) := by
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, mul_assoc, ← Real.exp_add]
    congr 2
    have hs2 : ∑ i, -(a * sv i ^ 2) / 2 = -(a * Q) / 2 := by
      rw [← hQ, Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_div]
    rw [hs2, ha]; ring
  have hterm : ∀ i, sv i ^ ν i * Real.exp (-(a * sv i ^ 2) / 2) ≤
      Real.exp (ph (ν i) / 2) * Real.exp (-(ν i * Real.log a) / 2) := by
    intro i
    refine rpow_mul_exp_neg_sq_le_exp_ph_mul_exp_log (ν i) (sv i) a (hν i) (hs i) ha0 ?_
    rcases (hν i).eq_or_lt with h | h
    · exact Or.inl h.symm
    · right
      have hNi : ν i ≤ N := Finset.single_le_sum (fun j _ => hν j) (Finset.mem_univ i)
      have hNp : 0 < N := lt_of_lt_of_le h hNi
      rw [ha]
      have : 1 / (N + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
      linarith
  have hT : ∏ i, (sv i ^ ν i * Real.exp (-(a * sv i ^ 2) / 2)) ≤
      Real.exp ((∑ i, ph (ν i)) / 2) * Real.exp (-(N * Real.log a) / 2) := by
    calc _ ≤ ∏ i, (Real.exp (ph (ν i) / 2) * Real.exp (-(ν i * Real.log a) / 2)) :=
          Finset.prod_le_prod (fun i _ => mul_nonneg (Real.rpow_nonneg (hs i) _) (Real.exp_pos _).le)
            (fun i _ => hterm i)
      _ = _ := by
          rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Real.exp_sum, Finset.sum_div, hN,
            Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.sum_div]
  have hlog : -(N * Real.log a) ≤ 1 := by
    rcases hN0.eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · have hN1 : N + 1 ≠ 0 := (by linarith : (0:ℝ) < N + 1).ne'
      have hNne : N ≠ 0 := h0.ne'
      have haeq : a = N / (N + 1) := by
        rw [ha, eq_div_iff hN1, sub_mul, one_div, inv_mul_cancel₀ hN1]; ring
      have hapos : 0 < a := by rw [haeq]; positivity
      have h1 := Real.log_le_sub_one_of_pos (inv_pos.2 hapos)
      rw [Real.log_inv] at h1
      have h2 : a⁻¹ - 1 = 1 / N := by rw [haeq, inv_div]; field_simp; ring
      rw [h2] at h1
      have h3 := mul_le_mul_of_nonneg_left h1 h0.le
      rw [mul_one_div_cancel h0.ne'] at h3
      linarith
  rw [hsplit]
  calc (∏ i, (sv i ^ ν i * Real.exp (-(a * sv i ^ 2) / 2))) * Real.exp (-(1 / (N + 1)) * Q / 2)
      ≤ (Real.exp ((∑ i, ph (ν i)) / 2) * Real.exp (-(N * Real.log a) / 2)) *
          Real.exp (-(1 / (N + 1)) * Q / 2) := mul_le_mul_of_nonneg_right hT (Real.exp_pos _).le
    _ ≤ Real.exp ((∑ i, ph (ν i)) / 2) * Real.exp (1 / 2) * Real.exp (-(1 / (N + 1)) * Q / 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith))
          (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by ring

theorem blockIntegral_of (hG : GaussCoord) : BlockIntegral := by
  intro Pl ι _ _ W _ _ r ν s Th R S hν hs hsq hTh hR
  have hS : 0 ≤ S := by
    by_contra hneg
    push_neg at hneg
    have h0 := (norm_nonneg _).trans (hTh 0)
    have := mul_neg_of_neg_of_pos hneg (Real.exp_pos (nsq (0 : Pl × ι → ℂ) / 2))
    linarith
  have hN1 : ∀ τ, 0 < (∑ i, ν τ i) + 1 := fun τ => by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hν τ i
    linarith
  have hbpos : ∀ x : Pl × ι, 0 < 1 / ((∑ i, ν x.1 i) + 1) / 2 := fun x =>
    div_pos (div_pos one_pos (hN1 x.1)) two_pos
  have hGb := hG (Pl × ι) (fun x => 1 / ((∑ i, ν x.1 i) + 1) / 2) hbpos
  set C := ∏ τ, (Real.exp (1 / 2) * Real.exp ((∑ i, ph (ν τ i)) / 2)) with hC
  have hpt : ∀ u : Pl × ι → ℂ, ‖(Th u * (Real.exp (-(nsq u)) : ℂ)) • R u‖ ≤
      S * C * Real.exp (-∑ x : Pl × ι, 1 / ((∑ i, ν x.1 i) + 1) / 2 * ‖u x‖ ^ 2) := by
    intro u
    rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hsplitN : nsq u = ∑ τ, nsq (fun x => u (τ, x)) := by
      simp only [nsq]; rw [Fintype.sum_prod_type]
    have hplace : ∀ τ, (∏ i, s τ (fun x => u (τ, x)) i ^ ν τ i) * Real.exp (-(nsq fun x => u (τ, x)) / 2) ≤
        Real.exp (1 / 2) * Real.exp ((∑ i, ph (ν τ i)) / 2) *
          Real.exp (-(1 / ((∑ i, ν τ i) + 1)) * (nsq fun x => u (τ, x)) / 2) :=
      fun τ => placeBound r (ν τ) (s τ _) _ (hν τ) (hs τ _) (hsq τ _)
    have hexp : Real.exp (-∑ x : Pl × ι, 1 / ((∑ i, ν x.1 i) + 1) / 2 * ‖u x‖ ^ 2) =
        ∏ τ, Real.exp (-(1 / ((∑ i, ν τ i) + 1)) * (nsq fun x => u (τ, x)) / 2) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [nsq]
      rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have he : Real.exp (nsq u / 2) * Real.exp (-nsq u) = ∏ τ, Real.exp (-(nsq fun x => u (τ, x)) / 2) := by
      rw [← Real.exp_add, ← Real.exp_sum]
      congr 1
      rw [hsplitN, ← Finset.sum_neg_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun τ _ => by ring
    calc ‖Th u‖ * Real.exp (-nsq u) * ‖R u‖
        ≤ S * Real.exp (nsq u / 2) * Real.exp (-nsq u) * ∏ τ, ∏ i, s τ (fun x => u (τ, x)) i ^ ν τ i :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hTh u) (Real.exp_pos _).le) (hR u) (norm_nonneg _)
            (mul_nonneg (mul_nonneg hS (Real.exp_pos _).le) (Real.exp_pos _).le)
      _ = S * ∏ τ, ((∏ i, s τ (fun x => u (τ, x)) i ^ ν τ i) * Real.exp (-(nsq fun x => u (τ, x)) / 2)) := by
          rw [Finset.prod_mul_distrib, ← he]; ring
      _ ≤ S * ∏ τ, (Real.exp (1 / 2) * Real.exp ((∑ i, ph (ν τ i)) / 2) *
            Real.exp (-(1 / ((∑ i, ν τ i) + 1)) * (nsq fun x => u (τ, x)) / 2)) :=
          mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun τ _ => mul_nonneg
            (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hs τ _ i) _) (Real.exp_pos _).le)
            fun τ _ => hplace τ) hS
      _ = _ := by rw [hexp, Finset.prod_mul_distrib, hC, mul_assoc]
  have hint := norm_integral_le_of_norm_le (hGb.1.const_mul (S * C)) (Filter.Eventually.of_forall hpt)
  have hprod : ∏ x : Pl × ι, π / (1 / ((∑ i, ν x.1 i) + 1) / 2) =
      π ^ (Fintype.card Pl * Fintype.card ι) * ∏ τ, (2 * (∑ i, ν τ i) + 2) ^ Fintype.card ι := by
    rw [Fintype.prod_prod_type]
    have hb : ∀ τ, ∏ i : ι, π / (1 / ((∑ j, ν (τ, i).1 j) + 1) / 2) =
        π ^ Fintype.card ι * (2 * (∑ i, ν τ i) + 2) ^ Fintype.card ι := fun τ => by
      have hne := (hN1 τ).ne'
      have hi : ∀ i : ι, π / (1 / ((∑ j, ν (τ, i).1 j) + 1) / 2) = π * (2 * (∑ i, ν τ i) + 2) :=
        fun i => by first | (field_simp; ring) | field_simp
      rw [Finset.prod_congr rfl fun i _ => hi i, Finset.prod_const, Finset.card_univ, mul_pow]
    rw [Finset.prod_congr rfl fun τ _ => hb τ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      ← pow_mul, mul_comm (Fintype.card ι)]
  rw [integral_const_mul, hGb.2, hprod] at hint
  have hpi : (0 : ℝ) < π ^ (Fintype.card Pl * Fintype.card ι) := by positivity
  rw [div_le_iff₀ hpi]
  calc _ ≤ _ := hint
    _ = _ := by
      have hr : ∀ τ, Real.exp (1 / 2) * (2 * (∑ i, ν τ i) + 2) ^ Fintype.card ι *
          Real.exp ((∑ i, ph (ν τ i)) / 2) = (Real.exp (1 / 2) * Real.exp ((∑ i, ph (ν τ i)) / 2)) *
          (2 * (∑ i, ν τ i) + 2) ^ Fintype.card ι := fun τ => by ring
      rw [Finset.prod_congr rfl fun τ _ => hr τ, Finset.prod_mul_distrib, ← hC]
      ring

end Formalism.DimensionVariation
