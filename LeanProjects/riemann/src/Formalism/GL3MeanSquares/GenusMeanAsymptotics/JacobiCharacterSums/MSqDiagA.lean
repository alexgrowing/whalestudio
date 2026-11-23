import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2
open ArithmeticFunction (vonMangoldt)

def dA_KC : ℝ := Real.log 4 + 4

lemma dA_KC_pos : 0 < dA_KC := by
  have h : 0 < Real.log 4 := Real.log_pos (by norm_num)
  unfold dA_KC
  linarith

lemma dA_Icc_one_eq_Ioc (M : ℕ) : Icc 1 M = Ioc 0 M := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

lemma dA_sum_vM_le (N : ℕ) : ∑ n ∈ Icc 1 N, vonMangoldt n ≤ dA_KC * N := by
  have hθ : ∀ M : ℕ, ∑ n ∈ (Icc 1 M).filter Nat.Prime, vonMangoldt n ≤ M * Real.log 4 := by
    intro M
    have hsub : (Icc 1 M).filter Nat.Prime ⊆ (range (M + 1)).filter Nat.Prime := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hn ⊢
      exact ⟨by omega, hn.2⟩
    have hdvd := Finset.prod_dvd_prod_of_subset _ _ (fun n => n) hsub
    have hle : ∏ n ∈ (Icc 1 M).filter Nat.Prime, n ≤ primorial M :=
      Nat.le_of_dvd (primorial_pos M) hdvd
    have hpos : 0 < ∏ n ∈ (Icc 1 M).filter Nat.Prime, n :=
      Finset.prod_pos (fun n hn => (Finset.mem_filter.mp hn).2.pos)
    have hlog : ∑ n ∈ (Icc 1 M).filter Nat.Prime, vonMangoldt n
        = Real.log ((∏ n ∈ (Icc 1 M).filter Nat.Prime, n : ℕ) : ℝ) := by
      rw [Nat.cast_prod, Real.log_prod]
      · refine Finset.sum_congr rfl (fun n hn => ?_)
        rw [Finset.mem_filter] at hn
        exact ArithmeticFunction.vonMangoldt_apply_prime hn.2
      · intro n hn
        rw [Finset.mem_filter] at hn
        exact Nat.cast_ne_zero.mpr hn.2.ne_zero
    rw [hlog]
    calc Real.log ((∏ n ∈ (Icc 1 M).filter Nat.Prime, n : ℕ) : ℝ) ≤ Real.log (primorial M : ℝ) :=
          Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)
      _ ≤ Real.log ((4:ℝ) ^ M) :=
          Real.log_le_log (by exact_mod_cast primorial_pos M) (by exact_mod_cast primorial_le_4_pow M)
      _ = M * Real.log 4 := Real.log_pow 4 M
  have hR : ∀ M : ℕ, ∑ n ∈ (Icc 1 M).filter (fun n => ¬ n.Prime), vonMangoldt n
      ≤ ∑ n ∈ Icc 1 (M / 2), vonMangoldt n := by
    intro M
    have hinv : ∀ m ∈ (Icc 1 (M / 2)).filter IsPrimePow, m * m.minFac / (m * m.minFac).minFac = m := by
      intro m hm
      rw [Finset.mem_filter] at hm
      obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff _).mp hm.2
      rw [hp.pow_minFac hj.ne', ← pow_succ, hp.pow_minFac (show j + 1 ≠ 0 by omega), pow_succ,
        Nat.mul_div_cancel _ hp.pos]
    have hval : ∀ m ∈ (Icc 1 (M / 2)).filter IsPrimePow, vonMangoldt (m * m.minFac) = vonMangoldt m := by
      intro m hm
      rw [Finset.mem_filter] at hm
      obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff _).mp hm.2
      rw [hp.pow_minFac hj.ne', ← pow_succ,
        ArithmeticFunction.vonMangoldt_apply_pow (show j + 1 ≠ 0 by omega),
        ArithmeticFunction.vonMangoldt_apply_pow hj.ne']
    have hsub : ((Icc 1 M).filter (fun n => ¬ n.Prime)).filter IsPrimePow
        ⊆ ((Icc 1 (M / 2)).filter IsPrimePow).image (fun m => m * m.minFac) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨⟨hn1, hnM⟩, hnp⟩, hpp⟩ := hn
      rw [isPrimePow_nat_iff] at hpp
      obtain ⟨p, k, hp, hk, rfl⟩ := hpp
      have hk2 : 2 ≤ k := by
        by_contra hlt
        apply hnp
        rw [show k = 1 by omega, pow_one]
        exact hp
      rw [Finset.mem_image]
      refine ⟨p ^ (k - 1), ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨Nat.one_le_pow _ _ hp.pos, ?_⟩,
          (isPrimePow_nat_iff _).mpr ⟨p, k - 1, hp, by omega, rfl⟩⟩
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        calc p ^ (k - 1) * 2 ≤ p ^ (k - 1) * p := Nat.mul_le_mul_left _ hp.two_le
          _ = p ^ k := by rw [← pow_succ]; congr 1; omega
          _ ≤ M := hnM
      · show p ^ (k - 1) * (p ^ (k - 1)).minFac = p ^ k
        rw [hp.pow_minFac (by omega), ← pow_succ]
        congr 1
        omega
    calc ∑ n ∈ (Icc 1 M).filter (fun n => ¬ n.Prime), vonMangoldt n
        = ∑ n ∈ ((Icc 1 M).filter (fun n => ¬ n.Prime)).filter IsPrimePow, vonMangoldt n :=
          (Finset.sum_filter_of_ne (fun n _ hn => not_not.mp
            (fun h => hn (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h)))).symm
      _ ≤ ∑ n ∈ ((Icc 1 (M / 2)).filter IsPrimePow).image (fun m => m * m.minFac), vonMangoldt n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      _ = ∑ m ∈ (Icc 1 (M / 2)).filter IsPrimePow, vonMangoldt (m * m.minFac) :=
          Finset.sum_image (fun a ha b hb h =>
            (hinv a ha).symm.trans ((congrArg (fun t => t / t.minFac) h).trans (hinv b hb)))
      _ = ∑ m ∈ (Icc 1 (M / 2)).filter IsPrimePow, vonMangoldt m := Finset.sum_congr rfl hval
      _ ≤ ∑ n ∈ Icc 1 (M / 2), vonMangoldt n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hl4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hl4 : Real.log 4 ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num)
    linarith
  simp only [dA_KC]
  refine Nat.strong_induction_on N ?_
  intro N ih
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp [Finset.Icc_eq_empty_of_lt (show (0:ℕ) < 1 by norm_num)]
  have hN2 : N / 2 < N := Nat.div_lt_self hpos (by norm_num)
  have ih2 := ih (N / 2) hN2
  have hcast : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := Nat.cast_div_le
  have hcK := mul_le_mul_of_nonneg_left hcast (show (0:ℝ) ≤ Real.log 4 + 4 by linarith)
  have hN4 := mul_le_mul_of_nonneg_left hl4 (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 N) Nat.Prime]
  have h1 := hθ N
  have h2 := hR N
  nlinarith

lemma dA_vM_major (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (hg : ∀ n, 1 ≤ n → g (n + 1) ≤ g n) (N : ℕ) :
    ∑ n ∈ Icc 1 N, vonMangoldt n * g n ≤ dA_KC * ∑ n ∈ Icc 1 N, g n := by
  have key : ∀ M : ℕ, (∑ n ∈ Icc 1 M, vonMangoldt n * g n) - (∑ n ∈ Icc 1 M, vonMangoldt n) * g M
      ≤ dA_KC * ((∑ n ∈ Icc 1 M, g n) - (M : ℝ) * g M) := by
    intro M
    induction M with
    | zero => simp [Finset.Icc_eq_empty_of_lt (show (0:ℕ) < 1 by norm_num)]
    | succ M ih =>
      rw [Finset.sum_Icc_succ_top (show 1 ≤ M + 1 by omega),
        Finset.sum_Icc_succ_top (show 1 ≤ M + 1 by omega),
        Finset.sum_Icc_succ_top (show 1 ≤ M + 1 by omega)]
      have h1 : (∑ n ∈ Icc 1 M, vonMangoldt n) * (g M - g (M + 1))
          ≤ dA_KC * M * (g M - g (M + 1)) := by
        rcases Nat.eq_zero_or_pos M with h | h
        · subst h
          simp [Finset.Icc_eq_empty_of_lt (show (0:ℕ) < 1 by norm_num)]
        · exact mul_le_mul_of_nonneg_right (dA_sum_vM_le M) (by linarith [hg M h])
      push_cast
      linarith
  have h2 : (∑ n ∈ Icc 1 N, vonMangoldt n) * g N ≤ dA_KC * N * g N :=
    mul_le_mul_of_nonneg_right (dA_sum_vM_le N) (hg0 N)
  have h3 := key N
  linarith

lemma dA_sum_inv_le (N : ℕ) (hN : 1 ≤ N) : ∑ n ∈ Icc 1 N, (1 : ℝ) / n ≤ 1 + Real.log N := by
  induction N with
  | zero => omega
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h
      simp
    · rw [Finset.sum_Icc_succ_top (show 1 ≤ M + 1 by omega)]
      have ih' := ih (by omega)
      have hM : (0:ℝ) < M := Nat.cast_pos.mpr h
      have hM1 : (M:ℝ) + 1 ≠ 0 := by positivity
      have hlog : Real.log ((M:ℝ) / ((M:ℝ) + 1)) ≤ (M:ℝ) / ((M:ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div hM.ne' hM1] at hlog
      have e : (M:ℝ) / ((M:ℝ) + 1) - 1 = -(1 / ((M:ℝ) + 1)) := by
        rw [div_sub_one hM1]
        ring
      push_cast
      linarith

lemma dA_sum_split (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n ≤ 1) (T : ℕ) (B : ℝ)
    (hB : ∀ M, T ≤ M → ∑ n ∈ Ioc T M, u n ≤ B) (M : ℕ) : ∑ n ∈ Icc 1 M, u n ≤ T + B := by
  have hcard : ∀ K : ℕ, ∑ n ∈ Icc 1 K, u n ≤ K := fun K => by
    calc ∑ n ∈ Icc 1 K, u n ≤ ∑ n ∈ Icc 1 K, (1:ℝ) := Finset.sum_le_sum (fun n _ => hu1 n)
      _ = K := by simp
  have hB0 : 0 ≤ B := by simpa using hB T le_rfl
  rcases le_or_gt M T with h | h
  · have hMT : (M:ℝ) ≤ T := by exact_mod_cast h
    linarith [hcard M]
  · have h2 := hcard T
    rw [dA_Icc_one_eq_Ioc] at h2 ⊢
    rw [← Finset.sum_Ioc_consecutive u (Nat.zero_le T) h.le]
    linarith [hB M h.le]

lemma dA_tail_sq (T : ℕ) (hT : 1 ≤ T) (M : ℕ) (hM : T ≤ M) :
    ∑ n ∈ Ioc T M, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / T - 1 / M := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hTM ih =>
    rw [Finset.sum_Ioc_succ_top hTM]
    have hM : (0:ℝ) < M := Nat.cast_pos.mpr (by omega)
    have e : 1 / (M:ℝ) - 1 / ((M:ℝ) + 1) = 1 / ((M:ℝ) * ((M:ℝ) + 1)) := by
      rw [div_sub_div _ _ hM.ne' (by positivity)]
      ring
    have k : 1 / ((M:ℝ) + 1) ^ 2 ≤ 1 / ((M:ℝ) * ((M:ℝ) + 1)) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    push_cast
    linarith

lemma dA_tail_geo (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (T M : ℕ) (hM : T ≤ M) :
    ∑ i ∈ Ioc T M, r ^ i + r ^ M ≤ r ^ T := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hTM ih =>
    rw [Finset.sum_Ioc_succ_top hTM, pow_succ]
    have hp : 0 ≤ r ^ M := pow_nonneg hr0 M
    have hq := mul_le_mul_of_nonneg_left hr hp
    linarith

lemma dA_cN_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 0 ≤ cN x n := by
  simp only [cN]
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (le_min zero_le_one (div_nonneg hx (Nat.cast_nonneg n)))

lemma dA_one_le_of_exp_le {x : ℝ} (hx : Real.exp 1 ≤ x) : 1 ≤ x := by
  have h := Real.add_one_le_exp (1:ℝ)
  linarith

lemma dA_one_le_log_of_exp_le {x : ℝ} (hx : Real.exp 1 ≤ x) : 1 ≤ Real.log x := by
  calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) hx

lemma dA_one_le_floor_pow {x : ℝ} (hx : 1 ≤ x) : 1 ≤ ⌊x ^ 400⌋₊ := by
  apply Nat.le_floor
  rw [Nat.cast_one]
  exact one_le_pow₀ hx

lemma dA_log_le_of_le_floor {x : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ ⌊x ^ 400⌋₊) :
    Real.log n ≤ 400 * Real.log x := by
  have h1 : (n:ℝ) ≤ x ^ 400 :=
    (Nat.cast_le.mpr hn).trans (Nat.floor_le (pow_nonneg (by linarith) 400))
  have h2 : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  calc Real.log n ≤ Real.log (x ^ 400) := Real.log_le_log h2 h1
    _ = 400 * Real.log x := by rw [Real.log_pow]; norm_num

theorem sum_cN_le : ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, cN x n ≤ C * x * Real.log x := by
  refine ⟨dA_KC * 401, Real.exp 1, fun x hx => ?_⟩
  have hx1 := dA_one_le_of_exp_le hx
  have hlog := dA_one_le_log_of_exp_le hx
  have hx0 : 0 ≤ x := by linarith
  have hN1 := dA_one_le_floor_pow hx1
  have hlogN := dA_log_le_of_le_floor hx1 hN1 le_rfl
  have h1 := dA_vM_major (fun n => min 1 (x / n)) (fun n => le_min zero_le_one (div_nonneg hx0 (Nat.cast_nonneg n)))
    (fun n hn => by
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      apply min_le_min_left
      push_cast
      gcongr
      linarith) ⌊x ^ 400⌋₊
  have h2 : ∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, min 1 (x / (n : ℝ)) ≤ x * (1 + Real.log ⌊x ^ 400⌋₊) := by
    calc ∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, min 1 (x / (n : ℝ)) ≤ ∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, x * (1 / (n : ℝ)) :=
          sum_le_sum (fun n _ => by rw [mul_one_div]; exact min_le_right _ _)
      _ = x * ∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, 1 / (n : ℝ) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (dA_sum_inv_le _ hN1) hx0
  have h3 : x * (1 + Real.log ⌊x ^ 400⌋₊) ≤ x * (401 * Real.log x) :=
    mul_le_mul_of_nonneg_left (by linarith) hx0
  calc ∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, cN x n ≤ dA_KC * ∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, min 1 (x / (n : ℝ)) := h1
    _ ≤ dA_KC * (x * (401 * Real.log x)) := mul_le_mul_of_nonneg_left (h2.trans h3) dA_KC_pos.le
    _ = _ := by ring

lemma dA_sum_min_pow (x : ℝ) (hx : 1 ≤ x) (p : ℕ) (hp : 2 ≤ p) (L : ℕ) :
    Real.log p * ∑ i ∈ Icc 1 L, min 1 (x / (p : ℝ) ^ i) ≤ Real.log x + 2 * Real.log p := by
  have hp0 : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hlp : 0 < Real.log p := Real.log_pos (by linarith)
  have hx0 : (0:ℝ) < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  set T := ⌊Real.log x / Real.log p⌋₊ + 1 with hT
  have hTlt : Real.log x / Real.log p < (T:ℝ) := by
    rw [hT]
    push_cast
    exact Nat.lt_floor_add_one _
  have hTle : (T:ℝ) - 1 ≤ Real.log x / Real.log p := by
    rw [hT]
    push_cast
    linarith [Nat.floor_le (div_nonneg hlx hlp.le)]
  have hTlog : ((T:ℝ) - 1) * Real.log p ≤ Real.log x := (le_div_iff₀ hlp).mp hTle
  have hxT : x ≤ (p:ℝ) ^ T := by
    have h1 : Real.log x < Real.log ((p:ℝ) ^ T) := by
      rw [Real.log_pow]
      rwa [div_lt_iff₀ hlp] at hTlt
    exact ((Real.log_lt_log_iff hx0 (by positivity)).mp h1).le
  have hr0 : (0:ℝ) ≤ 1 / p := by positivity
  have hr : (1:ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp0
  have htail : ∀ M, T ≤ M → ∑ i ∈ Ioc T M, min 1 (x / (p:ℝ) ^ i) ≤ 1 := by
    intro M hM
    have hg := dA_tail_geo (1 / (p:ℝ)) hr0 hr T M hM
    have hpos : (0:ℝ) ≤ (1 / (p:ℝ)) ^ M := pow_nonneg hr0 M
    calc ∑ i ∈ Ioc T M, min 1 (x / (p:ℝ) ^ i) ≤ ∑ i ∈ Ioc T M, x * (1 / (p:ℝ)) ^ i :=
          Finset.sum_le_sum (fun i _ => (min_le_right _ _).trans
            (le_of_eq (by rw [one_div_pow, mul_one_div])))
      _ = x * ∑ i ∈ Ioc T M, (1 / (p:ℝ)) ^ i := by rw [Finset.mul_sum]
      _ ≤ x * (1 / (p:ℝ)) ^ T := mul_le_mul_of_nonneg_left (by linarith) hx0.le
      _ = x / (p:ℝ) ^ T := by rw [one_div_pow, mul_one_div]
      _ ≤ 1 := by rw [div_le_one (by positivity)]; exact hxT
  have hsplit := dA_sum_split (fun i => min 1 (x / (p:ℝ) ^ i))
    (fun i => le_min zero_le_one (div_nonneg hx0.le (by positivity)))
    (fun i => min_le_left _ _) T 1 htail L
  have hmul := mul_le_mul_of_nonneg_left hsplit hlp.le
  linarith

private lemma le_pow_self_of_two_le (q k : ℕ) (hq : 2 ≤ q) : k ≤ q ^ k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    rw [pow_succ]
    have h2 := Nat.mul_le_mul_left (q ^ k) hq
    have h3 := pow_pos (show 0 < q by omega) k
    nlinarith

lemma primePowerSum_le_mul_log (x : ℝ) (hx : Real.exp 1 ≤ x) (p : ℕ) :
    sP (cN x) ⌊x ^ 400⌋₊ p ≤ 801 * Real.log x := by
  have hx1 := dA_one_le_of_exp_le hx
  have hlx := dA_one_le_log_of_exp_le hx
  have hx0 : (0:ℝ) ≤ x := by linarith
  have key : ∀ S : Finset ℕ, (∀ n ∈ S, n ∈ Icc 1 ⌊x ^ 400⌋₊ ∧ (IsPrimePow n ∧ n.minFac = p)) →
      ∑ n ∈ S, cN x n ≤ 801 * Real.log x := by
    intro S hS
    rcases S.eq_empty_or_nonempty with h | ⟨n0, hn0⟩
    · rw [h, Finset.sum_empty]
      linarith
    obtain ⟨hn0N, hn0pp, hn0min⟩ := hS n0 hn0
    rw [Finset.mem_Icc] at hn0N
    have hprime : p.Prime := by
      rw [← hn0min]
      exact Nat.minFac_prime hn0pp.ne_one
    have hpN : p ≤ ⌊x ^ 400⌋₊ := by
      rw [← hn0min]
      exact (Nat.minFac_le (by omega)).trans hn0N.2
    have hlogp : Real.log p ≤ 400 * Real.log x :=
      dA_log_le_of_le_floor hx1 hprime.one_lt.le hpN
    have hsub : S ⊆ (Icc 1 ⌊x ^ 400⌋₊).image (fun k => p ^ k) := by
      intro n hn
      obtain ⟨hnN, hnpp, hnmin⟩ := hS n hn
      rw [Finset.mem_Icc] at hnN
      rw [isPrimePow_nat_iff] at hnpp
      obtain ⟨q, k, hq, hk, rfl⟩ := hnpp
      rw [hq.pow_minFac hk.ne'] at hnmin
      subst hnmin
      rw [Finset.mem_image]
      exact ⟨k, Finset.mem_Icc.mpr ⟨hk, (le_pow_self_of_two_le q k hq.two_le).trans hnN.2⟩, rfl⟩
    calc ∑ n ∈ S, cN x n ≤ ∑ n ∈ (Icc 1 ⌊x ^ 400⌋₊).image (fun k => p ^ k), cN x n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => dA_cN_nonneg hx0 n)
      _ = ∑ k ∈ Icc 1 ⌊x ^ 400⌋₊, cN x (p ^ k) :=
          Finset.sum_image (fun a _ b _ h => Nat.pow_right_injective hprime.two_le h)
      _ = Real.log p * ∑ k ∈ Icc 1 ⌊x ^ 400⌋₊, min 1 (x / (p:ℝ) ^ k) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k hk => ?_)
          rw [Finset.mem_Icc] at hk
          simp only [cN, ArithmeticFunction.vonMangoldt_apply_pow (show k ≠ 0 by omega),
            ArithmeticFunction.vonMangoldt_apply_prime hprime, Nat.cast_pow]
      _ ≤ Real.log x + 2 * Real.log p := dA_sum_min_pow x hx1 p hprime.two_le _
      _ ≤ 801 * Real.log x := by linarith
  simp only [sP]
  exact key _ (fun n hn => Finset.mem_filter.mp hn)

theorem exists_primePowerSum_le : ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ p : ℕ, sP (cN x) ⌊x ^ 400⌋₊ p ≤ C * Real.log x := ⟨801, Real.exp 1, fun x hx p => primePowerSum_le_mul_log x hx p⟩

lemma dA_sum_min_sq (x : ℝ) (hx : 1 ≤ x) (M : ℕ) :
    ∑ m ∈ Icc 1 M, min 1 (x / (m : ℝ) ^ 2) ≤ 3 * Real.sqrt x := by
  have hs1 : 1 ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt hx
    rwa [Real.sqrt_one] at h
  have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hT1 : 1 ≤ ⌊Real.sqrt x⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; exact hs1)
  have hTgt : Real.sqrt x < (⌊Real.sqrt x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hTpos : (0:ℝ) < ⌊Real.sqrt x⌋₊ := Nat.cast_pos.mpr (by omega)
  have hT1' : (1:ℝ) ≤ ⌊Real.sqrt x⌋₊ := by exact_mod_cast hT1
  have h2T : Real.sqrt x ≤ 2 * (⌊Real.sqrt x⌋₊ : ℝ) := by linarith
  have htail : ∀ K, ⌊Real.sqrt x⌋₊ ≤ K →
      ∑ m ∈ Ioc ⌊Real.sqrt x⌋₊ K, min 1 (x / (m:ℝ) ^ 2) ≤ 2 * Real.sqrt x := by
    intro K hK
    have h1 := dA_tail_sq ⌊Real.sqrt x⌋₊ hT1 K hK
    have hK0 : (0:ℝ) ≤ 1 / (K:ℝ) := by positivity
    calc ∑ m ∈ Ioc ⌊Real.sqrt x⌋₊ K, min 1 (x / (m:ℝ) ^ 2)
        ≤ ∑ m ∈ Ioc ⌊Real.sqrt x⌋₊ K, x * (1 / (m:ℝ) ^ 2) :=
          Finset.sum_le_sum (fun m _ => (min_le_right _ _).trans (le_of_eq (by rw [mul_one_div])))
      _ = x * ∑ m ∈ Ioc ⌊Real.sqrt x⌋₊ K, 1 / (m:ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ x * (1 / (⌊Real.sqrt x⌋₊ : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ ≤ 2 * Real.sqrt x := by
          rw [mul_one_div, div_le_iff₀ hTpos]
          nlinarith [mul_le_mul_of_nonneg_left h2T (Real.sqrt_nonneg x)]
  have hs := dA_sum_split (fun m => min 1 (x / (m:ℝ) ^ 2))
    (fun m => le_min zero_le_one (div_nonneg (by linarith) (by positivity)))
    (fun m => min_le_left _ _) ⌊Real.sqrt x⌋₊ (2 * Real.sqrt x) htail M
  have hTle : (⌊Real.sqrt x⌋₊ : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
  linarith

theorem RR_cN_le : ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (m₀ : ℕ) (y : ℝ), 1 ≤ y →
    (∀ p : ℕ, p.Prime → p ∣ m₀ → p ≤ ⌊x ^ 400⌋₊ → (p : ℝ) ≤ y) →
    RR (cN x) m₀ ⌊x ^ 400⌋₊ ≤ C * (Real.sqrt x + y * Real.log x) := by
  refine ⟨3 * dA_KC + 801, Real.exp 1, fun x hx m₀ y hy hpy => ?_⟩
  have hx1 := dA_one_le_of_exp_le hx
  have hlx := dA_one_le_log_of_exp_le hx
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hK := dA_KC_pos
  have hsq0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hylx : 0 ≤ y * Real.log x := mul_nonneg (by linarith) (by linarith)
  have key : ∀ S : Finset ℕ, (∀ n ∈ S, n ∈ Icc 1 ⌊x ^ 400⌋₊ ∧ (IsPrimePow n ∧
      (Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀))) →
      ∑ n ∈ S, cN x n ≤ (3 * dA_KC + 801) * (Real.sqrt x + y * Real.log x) := by
    intro S hS
    have hA : ∑ n ∈ S.filter (fun n => Even (n.factorization n.minFac)), cN x n
        ≤ dA_KC * (3 * Real.sqrt x) := by
      have hsubA : S.filter (fun n => Even (n.factorization n.minFac))
          ⊆ (Icc 1 ⌊x ^ 400⌋₊).image (fun m => m ^ 2) := by
        intro n hn
        rw [Finset.mem_filter] at hn
        obtain ⟨hnS, hev⟩ := hn
        obtain ⟨hnN, hnpp, -⟩ := hS n hnS
        rw [Finset.mem_Icc] at hnN
        rw [isPrimePow_nat_iff] at hnpp
        obtain ⟨q, k, hq, hk, rfl⟩ := hnpp
        rw [hq.pow_minFac hk.ne'] at hev
        simp [Nat.factorization_pow, hq.factorization_self] at hev
        obtain ⟨j, rfl⟩ := hev
        rw [Finset.mem_image]
        have h1 : 1 ≤ q ^ j := Nat.one_le_pow _ _ hq.pos
        refine ⟨q ^ j, Finset.mem_Icc.mpr ⟨h1, ?_⟩, by show (q ^ j) ^ 2 = q ^ (j + j); ring⟩
        calc q ^ j ≤ (q ^ j) ^ 2 := by nlinarith
          _ = q ^ (j + j) := by ring
          _ ≤ _ := hnN.2
      have hgm : ∀ m : ℕ, 1 ≤ m → min 1 (x / ((m + 1 : ℕ) : ℝ) ^ 2) ≤ min 1 (x / (m : ℝ) ^ 2) := by
        intro m hm
        apply min_le_min_left
        have hm1 : (0:ℝ) < m := Nat.cast_pos.mpr (by omega)
        have hm0 : (0:ℝ) < (m:ℝ) ^ 2 := by positivity
        exact div_le_div_of_nonneg_left hx0 hm0 (by push_cast; nlinarith)
      have hmaj := dA_vM_major (fun m => min 1 (x / (m : ℝ) ^ 2))
        (fun m => le_min zero_le_one (div_nonneg hx0 (by positivity))) hgm ⌊x ^ 400⌋₊
      have hsq := dA_sum_min_sq x hx1 ⌊x ^ 400⌋₊
      calc ∑ n ∈ S.filter (fun n => Even (n.factorization n.minFac)), cN x n
          ≤ ∑ n ∈ (Icc 1 ⌊x ^ 400⌋₊).image (fun m => m ^ 2), cN x n :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubA (fun n _ _ => dA_cN_nonneg hx0 n)
        _ = ∑ m ∈ Icc 1 ⌊x ^ 400⌋₊, cN x (m ^ 2) :=
            Finset.sum_image (fun a _ b _ h => Nat.pow_left_injective (by norm_num) h)
        _ = ∑ m ∈ Icc 1 ⌊x ^ 400⌋₊, vonMangoldt m * min 1 (x / (m : ℝ) ^ 2) := by
            refine Finset.sum_congr rfl (fun m _ => ?_)
            simp only [cN, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (2:ℕ) ≠ 0),
              Nat.cast_pow]
        _ ≤ dA_KC * ∑ m ∈ Icc 1 ⌊x ^ 400⌋₊, min 1 (x / (m : ℝ) ^ 2) := hmaj
        _ ≤ dA_KC * (3 * Real.sqrt x) := mul_le_mul_of_nonneg_left hsq hK.le
    have hB : ∑ n ∈ S.filter (fun n => ¬ Even (n.factorization n.minFac)), cN x n
        ≤ y * (801 * Real.log x) := by
      have hmaps : ∀ n ∈ S.filter (fun n => ¬ Even (n.factorization n.minFac)),
          n.minFac ∈ Icc 1 ⌊y⌋₊ := by
        intro n hn
        rw [Finset.mem_filter] at hn
        obtain ⟨hnS, hodd⟩ := hn
        obtain ⟨hnN, hnpp, hor⟩ := hS n hnS
        rw [Finset.mem_Icc] at hnN
        have hdvd : n.minFac ∣ m₀ := hor.resolve_left hodd
        have hpr : n.minFac.Prime := Nat.minFac_prime hnpp.ne_one
        have hle : n.minFac ≤ ⌊x ^ 400⌋₊ := (Nat.minFac_le (by omega)).trans hnN.2
        exact Finset.mem_Icc.mpr ⟨hpr.one_lt.le, Nat.le_floor (hpy n.minFac hpr hdvd hle)⟩
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      calc _ ≤ ∑ p ∈ Icc 1 ⌊y⌋₊, 801 * Real.log x := by
            refine Finset.sum_le_sum (fun p _ => ?_)
            refine le_trans ?_ (primePowerSum_le_mul_log x hx p)
            simp only [sP]
            refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_)
              (fun n _ _ => dA_cN_nonneg hx0 n)
            rw [Finset.mem_filter] at hn
            obtain ⟨hn1, hn2⟩ := hn
            rw [Finset.mem_filter] at hn1
            obtain ⟨hnS, -⟩ := hn1
            obtain ⟨hnN, hnpp, -⟩ := hS n hnS
            exact Finset.mem_filter.mpr ⟨hnN, hnpp, hn2⟩
        _ = (⌊y⌋₊ : ℝ) * (801 * Real.log x) := by simp
        _ ≤ y * (801 * Real.log x) :=
            mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) (by linarith)
    rw [← Finset.sum_filter_add_sum_filter_not S (fun n => Even (n.factorization n.minFac))]
    refine (add_le_add hA hB).trans ?_
    nlinarith [mul_nonneg hK.le hylx]
  simp only [RR]
  exact key _ (fun n hn => Finset.mem_filter.mp hn)

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
