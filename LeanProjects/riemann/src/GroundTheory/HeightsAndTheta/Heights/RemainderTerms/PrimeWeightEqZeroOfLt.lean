import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Elementary
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

noncomputable section

namespace Elem

def primeWeight (B : ℝ) (i : ℕ) : ℝ := if i.Prime ∧ B < i then Real.log i else 0

theorem primeWeight_nonneg (B : ℝ) (i : ℕ) : 0 ≤ primeWeight B i := by
  unfold primeWeight
  split_ifs
  · exact Real.log_natCast_nonneg i
  · exact le_rfl

theorem sum_primeWeight_le (B : ℝ) (K : ℕ) :
    ∑ i ∈ range (K + 1), primeWeight B i ≤ K * Real.log 4 := by
  have hθ := ChebyshevThetaBound.intersectionNumber_baseChange (K : ℝ) (Nat.cast_nonneg K)
  rw [Nat.floor_natCast] at hθ
  refine le_trans ?_ hθ
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  unfold primeWeight
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd h1.1 h2
  · exact Real.log_natCast_nonneg i
  · exact le_rfl

theorem primeWeight_eq_zero_of_lt (B : ℝ) (hB : 0 ≤ B) {i : ℕ} (hi : i < ⌊B⌋₊ + 1) :
    primeWeight B i = 0 := by
  unfold primeWeight
  rw [if_neg]
  rintro ⟨_, h⟩
  have : (i : ℝ) ≤ B := by
    have := Nat.le_floor_iff hB |>.mp (Nat.lt_succ_iff.mp hi)
    exact this
  linarith

theorem abel_step (B : ℝ) (hB : 0 < B) (j : ℕ) :
    (∑ i ∈ range (⌊B⌋₊ + 1 + j), primeWeight B i / (i : ℝ) ^ 2) -
        (∑ i ∈ range (⌊B⌋₊ + 1 + j), primeWeight B i) / ((⌊B⌋₊ + 1 + j : ℕ) : ℝ) ^ 2 ≤
      2 * Real.log 4 * (1 / ((⌊B⌋₊ + 1 : ℕ) : ℝ) - 1 / ((⌊B⌋₊ + 1 + j : ℕ) : ℝ)) := by
  set M := ⌊B⌋₊ + 1 with hM
  induction j with
  | zero =>
    have h0 : ∀ i ∈ range (M + 0), primeWeight B i = 0 := fun i hi =>
      primeWeight_eq_zero_of_lt B hB.le (by have := Finset.mem_range.mp hi; omega)
    rw [Finset.sum_eq_zero (fun i hi => by rw [h0 i hi, zero_div]),
      Finset.sum_eq_zero h0]
    simp
  | succ j ih =>
    set K := M + j with hK
    have hK1 : (1 : ℝ) ≤ K := by
      have : 1 ≤ K := by omega
      exact_mod_cast this
    have hKpos : (0 : ℝ) < K := by linarith
    rw [show M + (j + 1) = K + 1 by omega] at *
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    set S := ∑ i ∈ range K, primeWeight B i / (i : ℝ) ^ 2
    set G := ∑ i ∈ range K, primeWeight B i
    set g := primeWeight B K
    have hG1 : G + g ≤ K * Real.log 4 := by
      have := sum_primeWeight_le B K
      rw [Finset.sum_range_succ] at this
      exact this
    have hG1nn : 0 ≤ G + g := by
      have : 0 ≤ ∑ i ∈ range (K + 1), primeWeight B i :=
        Finset.sum_nonneg (fun i _ => primeWeight_nonneg B i)
      rw [Finset.sum_range_succ] at this
      exact this
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    push_cast at ih ⊢

    have hdiff : (S + g / (K : ℝ) ^ 2 - (G + g) / ((K : ℝ) + 1) ^ 2) -
        (S - G / (K : ℝ) ^ 2) = (G + g) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2) := by
      field_simp
      ring
    have hnn : 0 ≤ 1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2 := by
      rw [sub_nonneg]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hstep : (G + g) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2) ≤
        2 * Real.log 4 * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1)) := by
      calc (G + g) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2)
          ≤ (K * Real.log 4) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2) :=
            mul_le_mul_of_nonneg_right hG1 hnn
        _ = Real.log 4 * ((2 * K + 1) / (K * ((K : ℝ) + 1) ^ 2)) := by
            field_simp
            ring
        _ ≤ Real.log 4 * (2 * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1))) := by
            apply mul_le_mul_of_nonneg_left _ hlog4
            rw [show (2 : ℝ) * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1)) = 2 / (K * ((K : ℝ) + 1)) by
              field_simp; ring]
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
        _ = 2 * Real.log 4 * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1)) := by ring
    have ih' : S - G / (K : ℝ) ^ 2 ≤ 2 * Real.log 4 * (1 / ((M : ℕ) : ℝ) - 1 / (K : ℝ)) := by
      simpa using ih
    have : S + g / (K : ℝ) ^ 2 - (G + g) / ((K : ℝ) + 1) ^ 2 ≤
        2 * Real.log 4 * (1 / ((M : ℕ) : ℝ) - 1 / ((K : ℝ) + 1)) := by
      linarith
    simpa using this

theorem prime_partial_le (B : ℝ) (hB : 0 < B) (K : ℕ) :
    ∑ i ∈ range K, primeWeight B i / (i : ℝ) ^ 2 ≤ 2 * Real.log 4 / B := by
  set M := ⌊B⌋₊ + 1 with hM
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hMB : B < (M : ℝ) := by
    rw [hM]; push_cast; exact Nat.lt_floor_add_one B
  have hMpos : (0 : ℝ) < M := lt_trans hB hMB
  have hfinal : 2 * Real.log 4 / (M : ℝ) ≤ 2 * Real.log 4 / B :=
    div_le_div_of_nonneg_left (by positivity) hB hMB.le
  rcases lt_or_ge K M with hK | hK
  · rw [Finset.sum_eq_zero]
    · positivity
    · intro i hi
      rw [primeWeight_eq_zero_of_lt B hB.le (lt_trans (Finset.mem_range.mp hi) hK), zero_div]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hK
    have hW := abel_step B hB j
    rw [← hM] at hW
    set K := M + j
    have hKpos : (0 : ℝ) < (K : ℝ) := by
      have : (M : ℝ) ≤ K := by exact_mod_cast (Nat.le_add_right M j)
      linarith
    have hG : ∑ i ∈ range K, primeWeight B i ≤ K * Real.log 4 := by
      calc ∑ i ∈ range K, primeWeight B i ≤ ∑ i ∈ range (K + 1), primeWeight B i :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
              (fun i _ _ => primeWeight_nonneg B i)
        _ ≤ K * Real.log 4 := sum_primeWeight_le B K
    have hGK : (∑ i ∈ range K, primeWeight B i) / (K : ℝ) ^ 2 ≤ Real.log 4 / K := by
      rw [div_le_div_iff₀ (by positivity) hKpos]
      nlinarith
    have h1 : 0 ≤ Real.log 4 / K := by positivity
    calc ∑ i ∈ range K, primeWeight B i / (i : ℝ) ^ 2
        ≤ 2 * Real.log 4 * (1 / (M : ℝ) - 1 / (K : ℝ)) + Real.log 4 / K := by linarith
      _ = 2 * Real.log 4 / (M : ℝ) - Real.log 4 / K := by ring
      _ ≤ 2 * Real.log 4 / (M : ℝ) := by linarith
      _ ≤ 2 * Real.log 4 / B := hfinal

end Elem

open Elem in

theorem PrimeLogSquareTail.intersectionNumber_baseChange : PrimeLogSquareTail.Statement := by
  intro B hB
  set s : Set ℕ := {p | p.Prime ∧ B < p}
  have hind : s.indicator (fun p : ℕ => Real.log p / (p : ℝ) ^ 2) =
      fun i => primeWeight B i / (i : ℝ) ^ 2 := by
    funext i
    by_cases h : i.Prime ∧ B < i
    · simp [s, Set.indicator_of_mem, h, primeWeight]
    · simp [s, Set.indicator_of_notMem, h, primeWeight]
  have hnn : ∀ i, 0 ≤ primeWeight B i / (i : ℝ) ^ 2 := fun i =>
    div_nonneg (primeWeight_nonneg B i) (by positivity)
  have hsum : Summable (fun i => primeWeight B i / (i : ℝ) ^ 2) :=
    summable_of_sum_range_le hnn (prime_partial_le B hB)
  have hsub : Summable (fun p : s => Real.log p / (p : ℝ) ^ 2) := by
    have := (summable_subtype_iff_indicator (f := fun p : ℕ => Real.log p / (p : ℝ) ^ 2)
      (s := s)).mpr (by rw [hind]; exact hsum)
    exact this
  refine ⟨hsub, ?_⟩
  have : ∑' p : s, Real.log p / (p : ℝ) ^ 2 ≤ 2 * Real.log 4 / B := by
    rw [tsum_subtype s (fun p : ℕ => Real.log p / (p : ℝ) ^ 2), hind]
    exact Real.tsum_le_of_sum_range_le hnn (prime_partial_le B hB)
  exact this

namespace Elem

def phiT (t : ℝ) : ℝ := (1 + Real.log t) / t

theorem phiT_nonneg {t : ℝ} (ht : 1 ≤ t) : 0 ≤ phiT t := by
  unfold phiT
  have := Real.log_nonneg ht
  positivity

theorem log_div_sq_le_phiT_sub (x : ℝ) (hx : 3 ≤ x) :
    Real.log (x + 1) / (x + 1) ^ 2 ≤ phiT x - phiT (x + 1) := by
  have hx0 : 0 < x := by linarith
  set L := Real.log (x + 1)
  set l := Real.log x
  have hlL : L - 1 / x ≤ l := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
    rw [Real.log_div (by linarith) hx0.ne'] at h
    have : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    linarith
  have hL : 1 + 1 / x ≤ L := by
    have h2 := Real.log_two_gt_d9
    have h4 : Real.log 4 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have h13 : 1 / x ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hx
    linarith
  have hmain : (1 + (L - 1 / x)) / x - (1 + L) / (x + 1) - L / (x + 1) ^ 2 =
      (L * x - x - 1) / (x ^ 2 * (x + 1) ^ 2) := by
    field_simp
    ring
  have hnum : 0 ≤ L * x - x - 1 := by
    have : (1 + 1 / x) * x = x + 1 := by field_simp
    nlinarith
  have h1 : (1 + (L - 1 / x)) / x ≤ (1 + l) / x :=
    div_le_div_of_nonneg_right (by linarith) hx0.le
  have h2 : 0 ≤ (L * x - x - 1) / (x ^ 2 * (x + 1) ^ 2) := by positivity
  unfold phiT
  linarith

def intWeight (B₀ : ℝ) (m : ℕ) : ℝ := if B₀ < m then Real.log m / (m : ℝ) ^ 2 else 0

theorem intWeight_nonneg (B₀ : ℝ) (m : ℕ) : 0 ≤ intWeight B₀ m := by
  unfold intWeight
  split_ifs
  · exact div_nonneg (Real.log_natCast_nonneg m) (by positivity)
  · exact le_rfl

theorem int_step (B₀ : ℝ) (hB : 16 ≤ B₀) (j : ℕ) :
    ∑ m ∈ range (⌊B₀⌋₊ + 1 + j), intWeight B₀ m ≤
      phiT (⌊B₀⌋₊ : ℝ) - phiT ((⌊B₀⌋₊ + j : ℕ) : ℝ) := by
  set n := ⌊B₀⌋₊ with hn
  have hn16 : 16 ≤ n := by
    rw [hn]; exact Nat.le_floor (by exact_mod_cast hB)
  induction j with
  | zero =>
    rw [Finset.sum_eq_zero]
    · simp
    · intro m hm
      have hm' : m ≤ n := by have := Finset.mem_range.mp hm; omega
      unfold intWeight
      rw [if_neg]
      intro h
      have : (m : ℝ) ≤ B₀ := by
        have := (Nat.le_floor_iff (by linarith)).mp hm'
        exact this
      linarith
  | succ j ih =>
    rw [show n + 1 + (j + 1) = (n + 1 + j) + 1 by omega, Finset.sum_range_succ]
    have hw : intWeight B₀ (n + 1 + j) =
        Real.log ((n + j : ℕ) + 1 : ℝ) / (((n + j : ℕ) : ℝ) + 1) ^ 2 := by
      unfold intWeight
      rw [if_pos]
      · push_cast; ring_nf
      · have : B₀ < ((n + 1 : ℕ) : ℝ) := by
          rw [hn]; push_cast; exact Nat.lt_floor_add_one B₀
        have h2 : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 + j : ℕ) : ℝ) := by exact_mod_cast (by omega)
        linarith
    have hk := log_div_sq_le_phiT_sub ((n + j : ℕ) : ℝ)
      (by have : 3 ≤ n + j := by omega
          exact_mod_cast this)
    rw [hw]
    have : ((n + (j + 1) : ℕ) : ℝ) = ((n + j : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [this]
    linarith

theorem int_partial_le (B₀ : ℝ) (hB : 16 ≤ B₀) (K : ℕ) :
    ∑ m ∈ range K, intWeight B₀ m ≤ 2 * (1 + Real.log B₀) / B₀ := by
  set n := ⌊B₀⌋₊ with hn
  have hB0 : 0 < B₀ := by linarith
  have hn16 : 16 ≤ n := by
    rw [hn]; exact Nat.le_floor (by exact_mod_cast hB)
  have hnle : (n : ℝ) ≤ B₀ := Nat.floor_le hB0.le
  have hnlt : B₀ < (n : ℝ) + 1 := Nat.lt_floor_add_one B₀
  have hn1 : (16 : ℝ) ≤ n := by exact_mod_cast hn16
  have hphi : phiT n ≤ 2 * (1 + Real.log B₀) / B₀ := by
    unfold phiT
    have hlog : Real.log n ≤ Real.log B₀ := Real.log_le_log (by linarith) hnle
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    rw [div_le_div_iff₀ (by linarith) hB0]
    nlinarith
  have hS : ∀ K, ∑ m ∈ range K, intWeight B₀ m ≤ phiT n := by
    intro K
    rcases le_or_gt K (n + 1) with hK | hK
    · calc ∑ m ∈ range K, intWeight B₀ m ≤ ∑ m ∈ range (n + 1 + 0), intWeight B₀ m :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
              (fun m _ _ => intWeight_nonneg B₀ m)
        _ ≤ phiT n - phiT ((n + 0 : ℕ) : ℝ) := int_step B₀ hB 0
        _ ≤ phiT n := by
            have := phiT_nonneg (t := ((n + 0 : ℕ) : ℝ)) (by push_cast; linarith)
            linarith
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hK.le
      calc ∑ m ∈ range (n + 1 + j), intWeight B₀ m ≤ phiT n - phiT ((n + j : ℕ) : ℝ) :=
            int_step B₀ hB j
        _ ≤ phiT n := by
            have := phiT_nonneg (t := ((n + j : ℕ) : ℝ)) (by push_cast; linarith)
            linarith
  exact (hS K).trans hphi

end Elem

open Elem in

theorem IntegerLogSquareTail.intersectionNumber_baseChange : IntegerLogSquareTail.Statement := by
  intro f N B₀ hf hN hB
  have hB16 : 16 ≤ B₀ := by
    have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  set s : Set ℕ := {m | B₀ < m}
  have hind : s.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ 2) = intWeight B₀ := by
    funext m
    by_cases h : B₀ < m
    · simp [s, Set.indicator_of_mem, h, intWeight]
    · simp [s, Set.indicator_of_notMem, h, intWeight]
  have hsum : Summable (intWeight B₀) :=
    summable_of_sum_range_le (intWeight_nonneg B₀) (int_partial_le B₀ hB16)
  have hsub : Summable (fun m : s => Real.log m / (m : ℝ) ^ 2) := by
    have := (summable_subtype_iff_indicator (f := fun m : ℕ => Real.log m / (m : ℝ) ^ 2)
      (s := s)).mpr (by rw [hind]; exact hsum)
    exact this
  refine ⟨hsub, ?_⟩
  have : ∑' m : s, Real.log m / (m : ℝ) ^ 2 ≤ 2 * (1 + Real.log B₀) / B₀ := by
    rw [tsum_subtype s (fun m : ℕ => Real.log m / (m : ℝ) ^ 2), hind]
    exact Real.tsum_le_of_sum_range_le (intWeight_nonneg B₀) (int_partial_le B₀ hB16)
  exact this

end

end RestTerms

end GroundTheory.Heights₂.Heights
