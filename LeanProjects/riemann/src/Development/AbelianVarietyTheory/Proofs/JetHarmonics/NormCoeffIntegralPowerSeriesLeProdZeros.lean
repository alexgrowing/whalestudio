import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

variable {K : Type} [NormedField K] in
private lemma summable_coeff_mul_pow [CompleteSpace K] (c : ℕ → K) (hc : ∀ n, ‖c n‖ ≤ 1) (y : K)
    (hy : ‖y‖ < 1) : Summable (fun n => c n * y ^ n) :=
  Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg y) hy) fun n => by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hc n)

variable {K : Type} [NormedField K] in
private lemma exists_quotient_by_linear_of_zero [IsUltrametricDist K] [CompleteSpace K] (c : ℕ → K)
    (hc : ∀ n, ‖c n‖ ≤ 1) (x : K) (hx : ‖x‖ < 1) (h0 : ∑' n, c n * x ^ n = 0) :
    ∃ d : ℕ → K, (∀ n, ‖d n‖ ≤ 1) ∧ c 0 = -(x * d 0) ∧ ∀ n, c (n + 1) = d n - x * d (n + 1) := by
  refine ⟨fun k => ∑' m, c (m + k + 1) * x ^ m, fun k => ?_, ?_, fun n => ?_⟩
  · refine IsUltrametricDist.norm_tsum_le_of_forall_le fun m => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (hc _) (by positivity) (pow_le_one₀ (norm_nonneg x) hx.le)
  · have hs := summable_coeff_mul_pow c hc x hx
    rw [hs.tsum_eq_zero_add] at h0
    have : ∑' m, c (m + 1) * x ^ (m + 1) = x * ∑' m, c (m + 0 + 1) * x ^ m := by
      rw [← tsum_mul_left]
      exact tsum_congr fun m => by rw [add_zero, pow_succ]; ring
    rw [this, pow_zero, mul_one] at h0
    linear_combination h0
  · have hs : Summable (fun m => c (m + n + 1) * x ^ m) :=
      summable_coeff_mul_pow (fun m => c (m + n + 1)) (fun m => hc _) x hx
    show c (n + 1) = ∑' m, c (m + n + 1) * x ^ m - x * ∑' m, c (m + (n + 1) + 1) * x ^ m
    rw [hs.tsum_eq_zero_add, ← tsum_mul_left]
    have : ∑' m, c (m + 1 + n + 1) * x ^ (m + 1) = ∑' m, x * (c (m + (n + 1) + 1) * x ^ m) :=
      tsum_congr fun m => by
        rw [show m + 1 + n + 1 = m + (n + 1) + 1 by omega, pow_succ]
        ring
    rw [this, pow_zero, mul_one, zero_add]
    ring

variable {K : Type} [NormedField K] in
private lemma tsum_eq_sub_mul_tsum [CompleteSpace K] (c d : ℕ → K) (hd : ∀ n, ‖d n‖ ≤ 1) (x : K)
    (hc : ∀ n, ‖c n‖ ≤ 1) (h0 : c 0 = -(x * d 0)) (hrel : ∀ n, c (n + 1) = d n - x * d (n + 1))
    (y : K) (hy : ‖y‖ < 1) :
    ∑' n, c n * y ^ n = (y - x) * ∑' n, d n * y ^ n := by
  have hsc := summable_coeff_mul_pow c hc y hy
  have hsd := summable_coeff_mul_pow d hd y hy
  have e1 : ∑' n, c n * y ^ n = c 0 + ∑' n, c (n + 1) * y ^ (n + 1) := by
    simpa using hsc.tsum_eq_zero_add
  have e2 : ∑' n, d n * y ^ n = d 0 + ∑' n, d (n + 1) * y ^ (n + 1) := by
    simpa using hsd.tsum_eq_zero_add
  have hA : Summable (fun n => y * (d n * y ^ n)) := hsd.mul_left y
  have hB : Summable (fun n => x * (d (n + 1) * y ^ (n + 1))) :=
    ((summable_nat_add_iff 1).mpr hsd).mul_left x
  have e3 : ∑' n, c (n + 1) * y ^ (n + 1) =
      y * ∑' n, d n * y ^ n - x * ∑' n, d (n + 1) * y ^ (n + 1) := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← hA.tsum_sub hB]
    exact tsum_congr fun n => by rw [hrel n, pow_succ]; ring
  rw [e1, e3, h0]
  linear_combination x * e2

variable {K : Type} [NormedField K] in
private lemma coeff_bounds_of_zeros [IsUltrametricDist K] [CompleteSpace K] (S : Finset K) :
    ∀ c : ℕ → K, (∀ n, ‖c n‖ ≤ 1) → (∀ x ∈ S, ‖x‖ < 1 ∧ ∑' n, c n * x ^ n = 0) →
      (∀ r : ℝ, 0 < r → r ≤ 1 → (∀ x ∈ S, r ≤ ‖x‖) → ∀ k, ‖c k‖ * r ^ k ≤ ∏ x ∈ S, ‖x‖) ∧
      (‖c S.card‖ = 1 → (∀ k < S.card, ‖c k‖ < 1) → ∏ x ∈ S, ‖x‖ = ‖c 0‖) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro c hc _
    refine ⟨fun r hr0 hr1 _ k => ?_, fun h1 _ => ?_⟩
    · rw [Finset.prod_empty]
      exact mul_le_one₀ (hc k) (by positivity) (pow_le_one₀ hr0.le hr1)
    · simpa using h1.symm
  | insert x S hxS ih =>
    intro c hc hz
    obtain ⟨hx, hx0⟩ := hz x (Finset.mem_insert_self x S)
    obtain ⟨d, hd, h0, hrel⟩ := exists_quotient_by_linear_of_zero c hc x hx hx0
    have hzd : ∀ y ∈ S, ‖y‖ < 1 ∧ ∑' n, d n * y ^ n = 0 := by
      intro y hy
      obtain ⟨hy1, hy0⟩ := hz y (Finset.mem_insert_of_mem hy)
      refine ⟨hy1, ?_⟩
      rw [tsum_eq_sub_mul_tsum c d hd x hc h0 hrel y hy1] at hy0
      have hne : y - x ≠ 0 := sub_ne_zero.mpr fun h => hxS (h ▸ hy)
      exact (mul_eq_zero.mp hy0).resolve_left hne
    obtain ⟨ih1, ih2⟩ := ih d hd hzd
    have hP : 0 ≤ ∏ y ∈ S, ‖y‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
    refine ⟨fun r hr0 hr1 hrS k => ?_, fun h1 hlt => ?_⟩
    · rw [Finset.prod_insert hxS]
      have hrx : r ≤ ‖x‖ := hrS x (Finset.mem_insert_self x S)
      have hrS' : ∀ y ∈ S, r ≤ ‖y‖ := fun y hy => hrS y (Finset.mem_insert_of_mem hy)
      have hb := ih1 r hr0 hr1 hrS'
      cases k with
      | zero =>
        rw [h0, norm_neg, norm_mul, pow_zero, mul_one]
        have := hb 0
        rw [pow_zero, mul_one] at this
        exact mul_le_mul_of_nonneg_left this (norm_nonneg x)
      | succ n =>
        have hm : ‖c (n + 1)‖ ≤ max ‖d n‖ (‖x‖ * ‖d (n + 1)‖) := by
          rw [hrel n, sub_eq_add_neg]
          simpa [norm_mul] using IsUltrametricDist.norm_add_le_max (d n) (-(x * d (n + 1)))
        have e1 : ‖d n‖ * r ^ (n + 1) ≤ ‖x‖ * ∏ y ∈ S, ‖y‖ := by
          rw [pow_succ, ← mul_assoc, mul_comm ‖x‖]
          exact mul_le_mul (hb n) hrx hr0.le hP
        have e2 : ‖x‖ * ‖d (n + 1)‖ * r ^ (n + 1) ≤ ‖x‖ * ∏ y ∈ S, ‖y‖ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (hb (n + 1)) (norm_nonneg x)
        calc ‖c (n + 1)‖ * r ^ (n + 1)
            ≤ max ‖d n‖ (‖x‖ * ‖d (n + 1)‖) * r ^ (n + 1) :=
              mul_le_mul_of_nonneg_right hm (by positivity)
          _ = max (‖d n‖ * r ^ (n + 1)) (‖x‖ * ‖d (n + 1)‖ * r ^ (n + 1)) :=
              max_mul_of_nonneg _ _ (by positivity)
          _ ≤ ‖x‖ * ∏ y ∈ S, ‖y‖ := max_le e1 e2
    · rw [Finset.card_insert_of_notMem hxS] at h1 hlt
      have hsmall : ∀ k, ‖x * d k‖ < 1 := fun k => by
        rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg x) (hd k)).trans_lt hx
      have hdk : ∀ k, d k = c (k + 1) + x * d (k + 1) := fun k => by rw [hrel k]; ring
      have hd1 : ‖d S.card‖ = 1 := by
        rw [hdk, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, h1]
        · exact max_eq_left (hsmall _).le
        · rw [h1]
          exact (hsmall _).ne'
      have hdlt : ∀ k < S.card, ‖d k‖ < 1 := fun k hk => by
        rw [hdk]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
          (max_lt (hlt (k + 1) (by omega)) (hsmall _))
      rw [Finset.prod_insert hxS, ih2 hd1 hdlt, h0, norm_neg, norm_mul]

theorem _root_.GlobalTheory.ConvSer.norm_coeff_le_prod_zeros : ∀ (K : Type) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (h : PowerSeries K) (S : Finset K),
    _root_.GlobalTheory.ConvSer.Intg h → (∀ x ∈ S, ‖x‖ < 1 ∧ _root_.GlobalTheory.ConvSer.ev1 h x = 0) →
    (∀ r : ℝ, 0 < r → r ≤ 1 → (∀ x ∈ S, r ≤ ‖x‖) → ∀ k, ‖PowerSeries.coeff k h‖ * r ^ k ≤
      ∏ x ∈ S, ‖x‖) ∧ (‖PowerSeries.coeff S.card h‖ = 1 → (∀ k < S.card,
      ‖PowerSeries.coeff k h‖ < 1) → ∏ x ∈ S, ‖x‖ = ‖PowerSeries.coeff 0 h‖) := by
  intro K _ _ _ h S hI hS
  exact coeff_bounds_of_zeros S (fun n => PowerSeries.coeff n h)
    (fun n => hI (Finsupp.single () n)) hS

end GlobalTheory.ConvSer
