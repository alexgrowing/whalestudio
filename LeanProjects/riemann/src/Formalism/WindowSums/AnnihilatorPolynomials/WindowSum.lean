import Formalism.WindowSums.Statement

noncomputable section

namespace Formalism.WindowSums

open Finset

lemma windowSum_count (a : ℤ) (L : ℕ) (r : ℤ) (hr : 0 < r) :
    ((((Finset.Ico a (a + L)).filter (fun x => r ∣ x)).card : ℕ) : ℝ) ≤ (L : ℝ) / (r : ℝ) + 1 := by
  have hmaps : ∀ x ∈ (Finset.Ico a (a + L)).filter (fun x => r ∣ x),
      (x - a) / r ∈ Finset.Icc (0 : ℤ) ((L : ℤ) / r) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ico] at hx
    simp only [Finset.mem_Icc]
    exact ⟨Int.ediv_nonneg (by linarith) hr.le, Int.ediv_le_ediv hr (by linarith)⟩
  have hinj : Set.InjOn (fun x => (x - a) / r)
      ((Finset.Ico a (a + L)).filter (fun x => r ∣ x) : Set ℤ) := by
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    obtain ⟨k, rfl⟩ := hx.2
    obtain ⟨m, rfl⟩ := hy.2
    simp only at hxy
    rw [show r * k - a = -a + r * k by ring, show r * m - a = -a + r * m by ring,
      Int.add_mul_ediv_left _ _ hr.ne', Int.add_mul_ediv_left _ _ hr.ne'] at hxy
    have : k = m := by linarith
    rw [this]
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  have hq0 : 0 ≤ (L : ℤ) / r := Int.ediv_nonneg (by positivity) hr.le
  rw [Int.card_Icc, sub_zero] at hcard
  have hc : ((((Finset.Ico a (a + L)).filter (fun x => r ∣ x)).card : ℕ) : ℝ) ≤
      (((L : ℤ) / r : ℤ) : ℝ) + 1 := by
    have h1 : ((((Finset.Ico a (a + L)).filter (fun x => r ∣ x)).card : ℕ) : ℤ) ≤ (L : ℤ) / r + 1 := by
      have := Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ (L : ℤ) / r + 1)
      omega
    exact_mod_cast h1
  have hdiv : (((L : ℤ) / r : ℤ) : ℝ) ≤ (L : ℝ) / (r : ℝ) := by
    rw [le_div_iff₀ (by exact_mod_cast hr)]
    exact_mod_cast Int.ediv_mul_le (L : ℤ) hr.ne'
  linarith

private theorem sum_range_one_div_pow_succ_eq (x : ℝ) (hx : 1 < x) (K : ℕ) :
    ∑ k ∈ Finset.range K, 1 / x ^ (k + 1) = (1 - 1 / x ^ K) / (x - 1) := by
  have hx0 : x - 1 ≠ 0 := by linarith
  have hxp : x ≠ 0 := by linarith
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    field_simp
    ring

theorem sum_padicValInt_le : WindowSum := by
  intro ℓ _ a L D S hS h0 hD
  have hℓ : ℓ.Prime := Fact.out
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.one_lt
  have hL0 : (0 : ℝ) ≤ (L : ℝ) / ((ℓ : ℝ) - 1) := div_nonneg (Nat.cast_nonneg _) (by linarith)
  rcases Nat.eq_zero_or_pos D with rfl | hDpos
  · have hzero : ∑ i ∈ S, padicValInt ℓ i = 0 := Finset.sum_eq_zero fun i hi =>
      (h0 ((abs_nonpos_iff.1 (by exact_mod_cast hD i hi)) ▸ hi)).elim
    rw [hzero]
    simpa [Real.logb_zero] using hL0
  have hv : ∀ i ∈ S, padicValInt ℓ i =
      ((Finset.range (Nat.log ℓ D)).filter (fun k => (ℓ : ℤ) ^ (k + 1) ∣ i)).card := by
    intro i hi
    have hi0 : i ≠ 0 := fun h => h0 (h ▸ hi)

    have hvK : padicValInt ℓ i ≤ Nat.log ℓ D := by
      have hdvd : (ℓ : ℤ) ^ padicValInt ℓ i ∣ i := (padicValInt_dvd_iff _ _).2 (Or.inr le_rfl)
      have h1 : ℓ ^ padicValInt ℓ i ∣ i.natAbs := by
        rw [← Int.natCast_dvd]
        exact_mod_cast hdvd
      have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 hi0) h1
      have h3 : i.natAbs ≤ D := by
        have h4 := hD i hi
        rw [← Int.natCast_natAbs] at h4
        exact_mod_cast h4
      exact Nat.le_log_of_pow_le hℓ.one_lt (h2.trans h3)
    have hf : (Finset.range (Nat.log ℓ D)).filter (fun k => (ℓ : ℤ) ^ (k + 1) ∣ i) =
        Finset.range (padicValInt ℓ i) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, padicValInt_dvd_iff, hi0, false_or]
      omega
    rw [hf, Finset.card_range]
  have hcount : ∀ k, ((S.filter (fun i => (ℓ : ℤ) ^ (k + 1) ∣ i)).card : ℝ) ≤
      (L : ℝ) / (ℓ : ℝ) ^ (k + 1) + 1 := by
    intro k
    have h1 := windowSum_count a L ((ℓ : ℤ) ^ (k + 1)) (pow_pos (by exact_mod_cast hℓ.pos) _)
    push_cast at h1
    refine le_trans ?_ h1
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hS)
  have hsum : ∑ i ∈ S, padicValInt ℓ i = ∑ k ∈ Finset.range (Nat.log ℓ D),
      (S.filter (fun i => (ℓ : ℤ) ^ (k + 1) ∣ i)).card := by
    rw [Finset.sum_congr rfl hv]
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hlog : ((Nat.log ℓ D : ℕ) : ℝ) ≤ Real.logb ℓ D := by
    rw [Real.le_logb_iff_rpow_le hℓ1 (by exact_mod_cast hDpos), Real.rpow_natCast]
    exact_mod_cast Nat.pow_log_le_self ℓ hDpos.ne'
  have h1 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hy : 0 ≤ 1 / (ℓ : ℝ) ^ Nat.log ℓ D := by positivity
  have hgeo : (L : ℝ) * ((1 - 1 / (ℓ : ℝ) ^ Nat.log ℓ D) / ((ℓ : ℝ) - 1)) ≤
      (L : ℝ) / ((ℓ : ℝ) - 1) := by
    rw [← mul_div_assoc, div_le_div_iff₀ h1 h1]
    nlinarith [Nat.cast_nonneg (α := ℝ) L, mul_nonneg (Nat.cast_nonneg (α := ℝ) L) hy]
  rw [hsum]
  push_cast
  calc ∑ k ∈ Finset.range (Nat.log ℓ D), ((S.filter (fun i => (ℓ : ℤ) ^ (k + 1) ∣ i)).card : ℝ)
      ≤ ∑ k ∈ Finset.range (Nat.log ℓ D), ((L : ℝ) / (ℓ : ℝ) ^ (k + 1) + 1) :=
        Finset.sum_le_sum fun k _ => hcount k
    _ = (L : ℝ) * ∑ k ∈ Finset.range (Nat.log ℓ D), 1 / (ℓ : ℝ) ^ (k + 1) + (Nat.log ℓ D : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, mul_one]
        congr 1
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ (L : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by
        rw [sum_range_one_div_pow_succ_eq _ hℓ1]
        linarith

end Formalism.WindowSums
