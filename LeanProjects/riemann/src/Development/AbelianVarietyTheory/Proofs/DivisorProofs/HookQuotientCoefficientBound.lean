import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookDeterminantRatioStatement

open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula

namespace GlobalTheory.FlagHook

theorem detE_eq_C_mul_det_pow {N : ℕ} (n : Fin N → ℕ) :
    detE n = C (∏ c, ((n c).factorial : ℝ))⁻¹ *
      Matrix.det (Matrix.of fun i c : Fin N => (X i : MvPolynomial (Fin N) ℝ) ^ n c) := by
  unfold detE
  have h := Matrix.det_mul_row (fun c : Fin N => (C (((n c).factorial : ℝ)⁻¹) : MvPolynomial (Fin N) ℝ))
    (Matrix.of fun i c : Fin N => (X i : MvPolynomial (Fin N) ℝ) ^ n c)
  rw [← Finset.prod_inv_distrib, map_prod, ← h]
  rfl

theorem prod_factorial_hookRho_mul (N k r : ℕ) (hr : r < N) :
    (∏ c, (hookRho N k r c).factorial) * (N - 1 - r).factorial =
      (∏ c, (rho N c).factorial) * (N - 1 + (k - r)).factorial := by
  unfold hookRho rho
  rw [Fin.prod_univ_eq_prod_range
      (fun c => (N - 1 - c + (if c = 0 then k - r else if c ≤ r then 1 else 0)).factorial) N,
    Fin.prod_univ_eq_prod_range (fun c => (N - 1 - c).factorial) N]
  obtain ⟨t, ht⟩ : ∃ t, N = (r + 1) + t := ⟨N - (r + 1), by omega⟩
  have e1 : ∀ f : ℕ → ℕ, ∏ c ∈ range N, f c =
      (∏ c ∈ range (r + 1), f c) * ∏ c ∈ range t, f (r + 1 + c) := by
    intro f
    rw [ht, Finset.prod_range_add]
  rw [e1, e1 (fun c => (N - 1 - c).factorial), Finset.prod_range_succ', Finset.prod_range_succ]
  have a1 : ∏ c ∈ range r,
      (N - 1 - (c + 1) + (if c + 1 = 0 then k - r else if c + 1 ≤ r then 1 else 0)).factorial =
      ∏ c ∈ range r, (N - 1 - c).factorial := by
    refine Finset.prod_congr rfl fun c hc => ?_
    have hc' := Finset.mem_range.1 hc
    rw [if_neg (by omega), if_pos (by omega)]
    congr 1
    omega
  have a2 : ∏ c ∈ range t,
      (N - 1 - (r + 1 + c) + (if r + 1 + c = 0 then k - r else if r + 1 + c ≤ r then 1 else 0)).factorial =
      ∏ c ∈ range t, (N - 1 - (r + 1 + c)).factorial := by
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [if_neg (by omega), if_neg (by omega), add_zero]
  rw [a1, a2]
  simp only [if_true, Nat.sub_zero]
  ring

theorem sum_coeff_le_eval_one {σ : Type} (S : MvPolynomial σ ℝ) (hS : ∀ m, 0 ≤ S.coeff m)
    (s : Finset (σ →₀ ℕ)) : ∑ m ∈ s, S.coeff m ≤ eval (fun _ => 1) S := by
  rw [eval_eq]
  simp only [one_pow, Finset.prod_const_one, mul_one]
  classical
  calc ∑ m ∈ s, S.coeff m ≤ ∑ m ∈ s ∪ S.support, S.coeff m :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun m _ _ => hS m
    _ = ∑ m ∈ S.support, S.coeff m := by
        symm
        refine Finset.sum_subset Finset.subset_union_right fun m _ hm => ?_
        exact notMem_support_iff.1 hm

theorem exists_hookR_eq_mul_detE_rho : ∀ (N k : ℕ), 1 ≤ k → k ≤ N → ∃ rr : MvPolynomial (Fin N) ℝ, rr.IsHomogeneous k ∧ hookR N k = rr * detE (rho N) ∧ ∑ m ∈ rr.support, |rr.coeff m| ≤ 2 ^ (k - 1) / (k.factorial : ℝ) := by
  intro N k hk1 hkN
  classical
  have H : ∀ r : ℕ, ∃ S : MvPolynomial (Fin N) ℝ, r < k → (S.IsHomogeneous k ∧ (∀ m, 0 ≤ S.coeff m) ∧
      eval (fun _ => 1) S = ((N + k - r - 1).choose k * (k - 1).choose r : ℕ) ∧
      Matrix.det (Matrix.of fun i c : Fin N => (X i : MvPolynomial (Fin N) ℝ) ^ hookRho N k r c) =
        S * Matrix.det (Matrix.of fun i c : Fin N => (X i : MvPolynomial (Fin N) ℝ) ^ rho N c)) := by
    intro r
    by_cases hr : r < k
    · obtain ⟨S, hS⟩ := GlobalTheory.T.hook_determinant_ratio N k r hr hkN
      exact ⟨S, fun _ => hS⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose S hS using H
  set P0 : ℝ := ∏ c, ((rho N c).factorial : ℝ) with hP0
  set P : ℕ → ℝ := fun r => ∏ c, ((hookRho N k r c).factorial : ℝ) with hP
  have P0pos : 0 < P0 := Finset.prod_pos fun c _ => by positivity
  have Ppos : ∀ r, 0 < P r := fun r => Finset.prod_pos fun c _ => by positivity
  refine ⟨∑ r ∈ range k, C ((-1 : ℝ) ^ r * (P0 / P r)) * S r, ?_, ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ fun r hr => ?_
    exact (hS r (Finset.mem_range.1 hr)).1.C_mul _
  · unfold hookR
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [detE_eq_C_mul_det_pow, detE_eq_C_mul_det_pow, (hS r (Finset.mem_range.1 hr)).2.2.2]
    have : (C ((-1 : ℝ) ^ r) * C (P r)⁻¹ : MvPolynomial (Fin N) ℝ) =
        C ((-1 : ℝ) ^ r * (P0 / P r)) * C P0⁻¹ := by
      rw [← map_mul, ← map_mul]
      congr 1
      have := P0pos.ne'
      have := (Ppos r).ne'
      field_simp
    change C ((-1 : ℝ) ^ r) * (C (P r)⁻¹ * _) = C ((-1 : ℝ) ^ r * (P0 / P r)) * S r * (C P0⁻¹ * _)
    rw [← mul_assoc, this]
    ring
  · generalize (∑ r ∈ range k, C ((-1 : ℝ) ^ r * (P0 / P r)) * S r).support = s
    have key : ∀ r ∈ range k, P0 / P r * eval (fun _ => 1) (S r) =
        ((k - 1).choose r : ℝ) / (k.factorial : ℝ) := by
      intro r hr
      have hr' := Finset.mem_range.1 hr
      rw [(hS r hr').2.2.1]
      have h1 := prod_factorial_hookRho_mul N k r (by omega)
      have h2 := Nat.choose_mul_factorial_mul_factorial (n := N + k - r - 1) (k := k) (by omega)
      rw [show N + k - r - 1 - k = N - 1 - r by omega] at h2
      rw [show N - 1 + (k - r) = N + k - r - 1 by omega, ← h2] at h1
      have h3 : P r * ((N - 1 - r).factorial : ℝ) =
          P0 * (((N + k - r - 1).choose k : ℝ) * (k.factorial : ℝ) * ((N - 1 - r).factorial : ℝ)) := by
        simp only [hP, hP0]
        exact_mod_cast h1
      have h4 : P r = P0 * (((N + k - r - 1).choose k : ℝ) * (k.factorial : ℝ)) := by
        have hf : ((N - 1 - r).factorial : ℝ) ≠ 0 := by positivity
        apply mul_right_cancel₀ hf
        rw [h3]; ring
      have h5 := (Ppos r).ne'
      have h6 : (k.factorial : ℝ) ≠ 0 := by positivity
      rw [div_mul_eq_mul_div, div_eq_div_iff h5 h6, h4]
      push_cast
      ring
    calc ∑ m ∈ s, |coeff m (∑ r ∈ range k, C ((-1 : ℝ) ^ r * (P0 / P r)) * S r)|
        ≤ ∑ m ∈ s, ∑ r ∈ range k, P0 / P r * coeff m (S r) := by
          refine Finset.sum_le_sum fun m _ => ?_
          rw [coeff_sum]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [coeff_C_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
            abs_of_pos (div_pos P0pos (Ppos r)),
            abs_of_nonneg ((hS r (Finset.mem_range.1 hr)).2.1 m)]
      _ = ∑ r ∈ range k, P0 / P r * ∑ m ∈ s, coeff m (S r) := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ ≤ ∑ r ∈ range k, P0 / P r * eval (fun _ => 1) (S r) := by
          refine Finset.sum_le_sum fun r hr => ?_
          exact mul_le_mul_of_nonneg_left
            (sum_coeff_le_eval_one _ (hS r (Finset.mem_range.1 hr)).2.1 s)
            (div_pos P0pos (Ppos r)).le
      _ = ∑ r ∈ range k, ((k - 1).choose r : ℝ) / (k.factorial : ℝ) := Finset.sum_congr rfl key
      _ = 2 ^ (k - 1) / (k.factorial : ℝ) := by
          rw [← Finset.sum_div]
          congr 1
          have := Nat.sum_range_choose (k - 1)
          rw [show k - 1 + 1 = k by omega] at this
          exact_mod_cast this

end GlobalTheory.FlagHook
