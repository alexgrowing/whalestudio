import Mathlib

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF

theorem near_far (c : ℝ) (A B : ℕ) (hc : 0 < c)
    (hT : ∀ (n K : ℕ) (z : Fin n → ℂ), 1 ≤ n → B * n ≤ K →
      (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) → (∀ i, ‖z i‖ ^ 2 ≤ 2 * (z i).re) →
      ∃ k : ℕ, K ≤ k ∧ k ≤ A * K ∧ c ^ K ≤ (∑ i, z i ^ k).re)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (N : ℕ) (u : Fin N → ℂ) (hu : ∀ i, ‖u i‖ ^ 2 ≤ (u i).re) (hi : ∃ i, 1 / 2 ≤ ‖u i‖)
    (K : ℕ) (hK2 : 2 ≤ K) (hKB : (B : ℝ) * (∑ i, (u i).re) ≤ ε ^ 2 * K) :
    ∃ j : ℕ, K ≤ j ∧ j ≤ A * K ∧
      c ^ K * (1 / 2) ^ j ≤ (∑ i, u i ^ j).re + ε ^ (j - 2) * ∑ i, (u i).re := by
  have hre : ∀ i, 0 ≤ (u i).re := fun i => le_trans (by positivity) (hu i)
  have hle1 : ∀ i, ‖u i‖ ≤ 1 := by
    intro i
    have h1 := hu i
    have h2 : (u i).re ≤ ‖u i‖ := Complex.re_le_norm _
    nlinarith [norm_nonneg (u i)]
  set near := (univ : Finset (Fin N)).filter (fun i => ε ≤ ‖u i‖) with hnear
  obtain ⟨i0, hi0⟩ := hi
  have hi0n : i0 ∈ near := by simp [hnear]; linarith
  have hne : near.Nonempty := ⟨i0, hi0n⟩
  obtain ⟨is, his, hmax⟩ := near.exists_max_image (fun i => ‖u i‖) hne
  set R := ‖u is‖ with hR
  have hR2 : 1 / 2 ≤ R := le_trans hi0 (hmax i0 hi0n)
  have hR0 : 0 < R := by linarith
  have hR1 : R ≤ 1 := hle1 is
  set n := near.card with hn

  have hcount : (n : ℝ) * ε ^ 2 ≤ ∑ i, (u i).re := by
    calc (n : ℝ) * ε ^ 2 = ∑ i ∈ near, ε ^ 2 := by simp [hn]
      _ ≤ ∑ i ∈ near, ‖u i‖ ^ 2 := by
          apply sum_le_sum; intro i hi
          have : ε ≤ ‖u i‖ := by simpa [hnear] using hi
          exact pow_le_pow_left₀ hε0.le this 2
      _ ≤ ∑ i ∈ near, (u i).re := sum_le_sum (fun i _ => hu i)
      _ ≤ ∑ i, (u i).re := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => hre i)
  have hBn : B * n ≤ K := by
    have h1 : (B : ℝ) * n * ε ^ 2 ≤ ε ^ 2 * K := by
      calc (B : ℝ) * n * ε ^ 2 = B * (n * ε ^ 2) := by ring
        _ ≤ B * ∑ i, (u i).re := mul_le_mul_of_nonneg_left hcount (by positivity)
        _ ≤ _ := hKB
    have h2 : (B : ℝ) * n ≤ K := by
      have : 0 < ε ^ 2 := by positivity
      nlinarith
    exact_mod_cast h2
  have hn1 : 1 ≤ n := Finset.card_pos.mpr hne
  let e := near.equivFin
  let z : Fin n → ℂ := fun k => u (e.symm k) / (R : ℂ)
  have hz : ∀ k, z k = u (e.symm k) / (R : ℂ) := fun k => rfl
  have hzn : ∀ k, ‖z k‖ = ‖u (e.symm k)‖ / R := by
    intro k; rw [hz, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
  obtain ⟨j, hKj, hjA, hj⟩ := hT n K z hn1 hBn
    (by
      intro k; rw [hzn, div_le_one hR0]
      exact hmax _ (e.symm k).2)
    (by
      refine ⟨e ⟨is, his⟩, ?_⟩
      rw [hzn]; simp [R, div_self (ne_of_gt hR0)])
    (by
      intro k
      rw [hzn, hz, Complex.div_ofReal_re]
      have h1 := hu (e.symm k)
      have h2 : ‖u (e.symm k)‖ ≤ R := hmax _ (e.symm k).2
      rw [div_pow, div_le_iff₀ (by positivity)]
      calc ‖u (e.symm k)‖ ^ 2 ≤ (u (e.symm k)).re := h1
        _ ≤ 2 * ((u (e.symm k)).re / R) * R ^ 2 := by
          rw [show 2 * ((u (e.symm k)).re / R) * R ^ 2 = (u (e.symm k)).re * (2 * R) by
            field_simp]
          have : 1 ≤ 2 * R := by linarith
          nlinarith [hre (e.symm k)])
  refine ⟨j, hKj, hjA, ?_⟩

  have hsumz : (∑ k, z k ^ j) * (R : ℂ) ^ j = ∑ i ∈ near, u i ^ j := by
    rw [Finset.sum_mul]
    rw [← Finset.sum_coe_sort near (fun i => u i ^ j)]
    rw [← e.symm.sum_comp]
    apply Finset.sum_congr rfl
    intro k _
    rw [hz, div_pow, div_mul_cancel₀]
    exact pow_ne_zero _ (by exact_mod_cast hR0.ne')
  have hnear_re : c ^ K * (1 / 2) ^ j ≤ (∑ i ∈ near, u i ^ j).re := by
    rw [← hsumz, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    have : (1 / 2 : ℝ) ^ j ≤ R ^ j := pow_le_pow_left₀ (by norm_num) hR2 j
    have hcK : 0 < c ^ K := pow_pos hc K
    nlinarith [pow_pos hR0 j]
  have hfar : -(ε ^ (j - 2) * ∑ i, (u i).re) ≤ (∑ i ∈ univ.filter (fun i => ¬ ε ≤ ‖u i‖), u i ^ j).re := by
    rw [Complex.re_sum]
    have hj2 : 2 ≤ j := le_trans hK2 hKj
    have : ∀ i ∈ univ.filter (fun i => ¬ ε ≤ ‖u i‖), -(ε ^ (j - 2) * (u i).re) ≤ (u i ^ j).re := by
      intro i hi
      have hlt : ‖u i‖ < ε := by simpa using hi
      have h1 : -(u i ^ j).re ≤ ‖u i‖ ^ j := by
        have := Complex.abs_re_le_norm (u i ^ j); rw [norm_pow] at this
        linarith [neg_abs_le (u i ^ j).re]
      have h2 : ‖u i‖ ^ j = ‖u i‖ ^ (j - 2) * ‖u i‖ ^ 2 := by
        rw [← pow_add]; congr 1; omega
      have h3 : ‖u i‖ ^ (j - 2) ≤ ε ^ (j - 2) := pow_le_pow_left₀ (norm_nonneg _) hlt.le _
      have h4 : ‖u i‖ ^ (j - 2) * ‖u i‖ ^ 2 ≤ ε ^ (j - 2) * (u i).re :=
        mul_le_mul h3 (hu i) (by positivity) (by positivity)
      linarith
    calc -(ε ^ (j - 2) * ∑ i, (u i).re) ≤ -(ε ^ (j - 2) * ∑ i ∈ univ.filter (fun i => ¬ ε ≤ ‖u i‖), (u i).re) := by
          have : ∑ i ∈ univ.filter (fun i => ¬ ε ≤ ‖u i‖), (u i).re ≤ ∑ i, (u i).re :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => hre i)
          have : 0 ≤ ε ^ (j - 2) := by positivity
          nlinarith
      _ = ∑ i ∈ univ.filter (fun i => ¬ ε ≤ ‖u i‖), -(ε ^ (j - 2) * (u i).re) := by
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      _ ≤ _ := sum_le_sum this
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Fin N)) (fun i => ε ≤ ‖u i‖) (fun i => u i ^ j)
  have hnr : (∑ x ∈ univ.filter (fun x => ε ≤ ‖u x‖), u x ^ j) = ∑ i ∈ near, u i ^ j := rfl
  rw [← hsplit, Complex.add_re, hnr]
  linarith

theorem pow_small_a (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (K : ℕ) (hK3 : 3 ≤ K) :
    (K : ℝ) * (q ^ 2 / 8) ^ (K - 1) ≤ q ^ K / 8 := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 3 := ⟨K - 3, by omega⟩
  have hB : (1 : ℝ) + (m + 1 : ℕ) * 7 ≤ (1 + 7) ^ (m + 1) := one_add_mul_le_pow (by norm_num) _
  push_cast at hB ⊢
  rw [div_pow, ← pow_mul]
  have h8 : (0 : ℝ) < 8 ^ (m + 2) := by positivity
  have hq' : q ^ (2 * (m + 2)) = q ^ (m + 3) * q ^ (m + 1) := by rw [← pow_add]; congr 1; ring
  have hqm : q ^ (m + 1) ≤ 1 := pow_le_one₀ hq0 hq1
  have hq3 : 0 ≤ q ^ (m + 3) := by positivity
  rw [hq', mul_div_assoc', div_le_div_iff₀ h8 (by norm_num)]
  have : (8 : ℝ) ^ (m + 2) = 8 * 8 ^ (m + 1) := by ring
  rw [this]
  have h1 : ((m : ℝ) + 3) ≤ 8 ^ (m + 1) := by norm_num at hB; linarith
  have h2 : ((m : ℝ) + 3) * (q ^ (m + 3) * q ^ (m + 1)) ≤ ((m : ℝ) + 3) * q ^ (m + 3) := by
    have : 0 ≤ (m : ℝ) + 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hqm hq3]
  nlinarith [mul_le_mul_of_nonneg_right h1 hq3]

theorem pow_small_b (q : ℝ) (hq0 : 0 ≤ q) (K : ℕ) (hK3 : 3 ≤ K) :
    (K : ℝ) * (q / 4) ^ K ≤ q ^ K / 8 := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 3 := ⟨K - 3, by omega⟩
  have hB : (1 : ℝ) + (m : ℕ) * 3 ≤ (1 + 3) ^ m := one_add_mul_le_pow (by norm_num) _
  rw [div_pow]
  have h4 : (4 : ℝ) ^ (m + 3) = 64 * 4 ^ m := by ring
  rw [h4]
  have hq3 : 0 ≤ q ^ (m + 3) := by positivity
  have h4p : (0 : ℝ) < 4 ^ m := by positivity
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
  push_cast
  norm_num at hB
  have : ((m : ℝ) + 3) * 8 ≤ 64 * 4 ^ m := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right this hq3]

theorem final_contra (q A K0 a b l : ℝ) (K : ℕ) (hq0 : 0 < q) (hq : q ≤ 1 / 4) (hl : l = -Real.log q)
    (hA : 1 ≤ A) (hK3 : 3 ≤ K) (hK0 : 0 < K0) (ha0 : 0 ≤ a) (ha : a * (2 * l + 2) ≤ 1) (hb : 0 ≤ b)
    (hKab : (K : ℝ) ≤ a * K0 + b) (hbig : b + 64 * A * Real.exp (l * b) < K0)
    (hmain : q ^ K ≤ 2 * A * K * Real.exp (-K0) + K * (q ^ 2 / 8) ^ (K - 1) + K * (q / 4) ^ K) : False := by
  have h1 := pow_small_a q hq0.le (by linarith) K hK3
  have h2 := pow_small_b q hq0.le K hK3
  have hl0 : 0 ≤ l := by
    rw [hl]; have := Real.log_nonpos hq0.le (by linarith); linarith
  have h3 : (3 / 4) * q ^ K ≤ 2 * A * K * Real.exp (-K0) := by linarith
  have hqK : Real.exp (-(K0 / 2) - l * b) ≤ q ^ K := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hq0, Real.exp_le_exp]
    have hlog : Real.log q = -l := by rw [hl]; ring
    rw [hlog]
    have hla : 2 * l * a ≤ 1 := by nlinarith
    nlinarith
  have hE := Real.exp_pos (l * b)
  have hsplit : Real.exp (-(K0 / 2) - l * b) * Real.exp (l * b) * Real.exp K0 = Real.exp (K0 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hexp : K0 ^ 2 / 8 ≤ Real.exp (K0 / 2) := by
    have := Real.pow_div_factorial_le_exp (x := K0 / 2) (by positivity) 2
    norm_num [Nat.factorial] at this; nlinarith
  have hKK : (K : ℝ) ≤ 2 * K0 := by
    have : a ≤ 1 / 2 := by nlinarith
    nlinarith
  have hexpK : Real.exp (-K0) * Real.exp K0 = 1 := by rw [← Real.exp_add]; simp

  have h4 : (3 / 4) * Real.exp (K0 / 2) ≤ 2 * A * K * Real.exp (l * b) := by
    have hx := mul_le_mul_of_nonneg_right (le_trans (mul_le_mul_of_nonneg_left hqK (by norm_num)) h3)
      (le_of_lt (mul_pos hE (Real.exp_pos K0)))
    rw [← hsplit]
    have : 2 * A * K * Real.exp (-K0) * (Real.exp (l * b) * Real.exp K0) = 2 * A * K * Real.exp (l * b) * (Real.exp (-K0) * Real.exp K0) := by ring
    rw [this, hexpK] at hx
    linarith
  have hAE : 0 ≤ A * Real.exp (l * b) := by positivity
  have h5 : (3 / 32) * K0 ^ 2 ≤ 4 * K0 * (A * Real.exp (l * b)) := by nlinarith
  have h6 : (3 / 32) * K0 ≤ 4 * (A * Real.exp (l * b)) := by nlinarith
  nlinarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
