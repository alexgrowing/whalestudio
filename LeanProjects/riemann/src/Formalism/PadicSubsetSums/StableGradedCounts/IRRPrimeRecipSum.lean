import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility

open Finset Nat

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace PrimeCountingLemmas

noncomputable def S (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N), (1 : ℝ) / p

theorem prime_of_gcd {r p : ℕ} (h1 : r < p) (h2 : p < (r + 1) * (r + 1))
    (h3 : Nat.gcd p (r.factorial) = 1) : p.Prime := by
  have hp2 : 2 ≤ p := by
    rcases Nat.lt_or_ge r 1 with hr | hr
    · nlinarith
    · omega
  by_contra hnp
  have hq := Nat.minFac_prime (by omega : p ≠ 1)
  have hqd : p.minFac ∣ p := Nat.minFac_dvd p
  have hqr : r < p.minFac := by
    by_contra hle
    push_neg at hle
    have h4 : p.minFac ∣ r.factorial := Nat.dvd_factorial hq.pos hle
    have h5 : p.minFac ∣ Nat.gcd p r.factorial := Nat.dvd_gcd hqd h4
    rw [h3] at h5
    exact hq.one_lt.ne' (Nat.dvd_one.1 h5)
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  nlinarith

def test (F r a b p : ℕ) : Bool :=
  Nat.ble (p + 3) a && Nat.blt b (2 * p) && Nat.blt r p && Nat.blt p ((r + 1) * (r + 1)) &&
    Nat.beq (Nat.gcd p F) 1

theorem test_spec {F r a b p : ℕ} (hF : F = r.factorial) (h : test F r a b p = true) :
    p.Prime ∧ b < 2 * p ∧ p + 3 ≤ a := by
  simp only [test, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨prime_of_gcd h3 h4 (hF ▸ h5), h2, h1⟩

def term (M F r a b p : ℕ) : ℕ := bif test F r a b p then M / p else 0

def bsum (t : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, lo => t lo
  | k + 1, lo => bsum t k lo + bsum t k (lo + 2 ^ k)

theorem bsum_eq (t : ℕ → ℕ) : ∀ k lo, bsum t k lo = ∑ p ∈ Finset.Ico lo (lo + 2 ^ k), t p := by
  intro k
  induction k with
  | zero =>
    intro lo
    simp [bsum]
  | succ k ih =>
    intro lo
    rw [bsum, ih, ih, Finset.sum_Ico_consecutive _ (Nat.le_add_right _ _) (Nat.le_add_right _ _), pow_succ,
      show lo + 2 ^ k + 2 ^ k = lo + 2 ^ k * 2 by ring]

def chk (M F r a b : ℕ) : Bool :=
  Nat.ble M (20 * bsum (term M F r a b) (Nat.log2 a) (b / 2))

theorem chk_sound {M F r a b : ℕ} (hM : 0 < M) (hF : F = r.factorial)
    (h : chk M F r a b = true) (N : ℕ)
    (haN : a ≤ N) (hNb : N ≤ b) : (1 : ℝ) / 20 ≤ S N := by
  simp only [chk, Nat.ble_eq] at h
  rw [bsum_eq] at h
  generalize Finset.Ico (b / 2) (b / 2 + 2 ^ Nat.log2 a) = I at h
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : (M : ℝ) ≤ 20 * ∑ p ∈ I, (term M F r a b p : ℝ) := by
    exact_mod_cast h
  have h2 : ∑ p ∈ I, (term M F r a b p : ℝ) ≤ M * S N := by
    unfold S
    rw [Finset.mul_sum]
    have e : ∀ p, (term M F r a b p : ℝ) =
        if test F r a b p = true then ((M / p : ℕ) : ℝ) else 0 := by
      intro p; unfold term; cases test F r a b p <;> simp
    simp only [e]
    rw [← Finset.sum_filter]
    refine (Finset.sum_le_sum (fun p _ => (Nat.cast_div_le : ((M / p : ℕ) : ℝ) ≤ M / p))).trans ?_
    refine (Finset.sum_le_sum_of_subset_of_nonneg
      (t := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N))
      ?_ ?_).trans (le_of_eq ?_)
    · intro p hp
      obtain ⟨h3, h4, h5⟩ := test_spec hF (Finset.mem_filter.mp hp).2
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, h3, by omega, by omega⟩
    · intro p _ _; positivity
    · refine Finset.sum_congr rfl (fun p _ => ?_)
      ring
  have h4 : (1 : ℝ) ≤ 20 * S N := by
    by_contra hc
    have := mul_lt_mul_of_pos_left (not_le.mp hc) hMr
    linarith
  linarith

def ladder (M F r T : ℕ) : ℕ → ℕ → Bool
  | 0, a => Nat.ble T a
  | f + 1, a => Nat.ble T a || (chk M F r a (a + a / 10) && ladder M F r T f (a + a / 10 + 1))

theorem ladder_sound {M F r T : ℕ} (hM : 0 < M) (hF : F = r.factorial) :
    ∀ (f a : ℕ), ladder M F r T f a = true →
    ∀ N, a ≤ N → N < T → (1 : ℝ) / 20 ≤ S N := by
  intro f
  induction f with
  | zero =>
    intro a h N h1 h2
    simp only [ladder, Nat.ble_eq] at h
    omega
  | succ f ih =>
    intro a h N h1 h2
    simp only [ladder, Bool.or_eq_true, Nat.ble_eq, Bool.and_eq_true] at h
    rcases h with h | ⟨h3, h4⟩
    · omega
    · by_cases hN : N ≤ a + a / 10
      · exact chk_sound hM hF h3 N h1 hN
      · exact ih _ h4 N (by omega) h2

theorem factorial_ladder_thirteen : ladder 1000000000 (Nat.factorial 13) 13 196 60 100 = true := by decide +kernel
theorem factorial_ladder_thirty_one : ladder 1000000000 (Nat.factorial 31) 31 1024 60 196 = true := by decide +kernel
theorem factorial_ladder_one_forty_one : ladder 1000000000 (Nat.factorial 141) 141 20000 60 1024 = true := by
  decide +kernel

theorem S_small (N : ℕ) (h1 : 100 ≤ N) (h2 : N < 20000) : (1 : ℝ) / 20 ≤ S N := by
  by_cases h3 : N < 196
  · exact ladder_sound (by norm_num) rfl 60 100 factorial_ladder_thirteen N h1 h3
  by_cases h4 : N < 1024
  · exact ladder_sound (by norm_num) rfl 60 196 factorial_ladder_thirty_one N (by omega) h4
  · exact ladder_sound (by norm_num) rfl 60 1024 factorial_ladder_one_forty_one N (by omega) h2

def upper (n : ℕ) : Finset ℕ := (Finset.range (2 * n + 1)).filter (fun p => p.Prime ∧ n < p)

theorem centralBinom_le (n : ℕ) (n_large : 2 < n) :
    centralBinom n ≤
      ((2 * n) ^ (primeCounting (sqrt (2 * n))) * 4 ^ (2 * n / 3)) * (2 * n) ^ (upper n).card := by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt n_large
  have n2_pos : 1 ≤ 2 * n := mul_pos (zero_lt_two' ℕ) n_pos
  let S0 := {p ∈ Finset.range (2 * n + 1) | Nat.Prime p}
  let f x := x ^ n.centralBinom.factorization x
  have hf : ∀ p, f p ≤ 2 * n := fun p => pow_factorization_choose_le (mul_pos two_pos n_pos)
  have h0 : ∏ x ∈ S0, f x = centralBinom n := by
    rw [← n.prod_pow_factorization_centralBinom]
    refine Finset.prod_filter_of_ne fun p _ h => ?_
    contrapose h; dsimp only [f]
    rw [factorization_eq_zero_of_not_prime n.centralBinom h, _root_.pow_zero]
  rw [← h0, ← Finset.prod_filter_mul_prod_filter_not S0 (· ≤ 2 * n / 3)]
  apply mul_le_mul'
  · rw [← Finset.prod_filter_mul_prod_filter_not _ (· ≤ sqrt (2 * n))]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod' fun p _ => hf p).trans ?_
      rw [Finset.prod_const]
      refine pow_right_mono₀ n2_pos ?_
      rw [← primesLE_card_eq_primeCounting]
      refine Finset.card_le_card fun x hx => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      obtain ⟨h3, _⟩ := Finset.mem_filter.1 h1
      exact mem_primesLE.mpr ⟨h2, (Finset.mem_filter.1 h3).2⟩
    · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
      refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
        obtain ⟨h3, _⟩ := Finset.mem_filter.1 h1
        refine (pow_right_mono₀ (Finset.mem_filter.1 h3).2.one_lt.le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 h2)
      · unfold primorial
        refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
        · intro p hp
          obtain ⟨h1, _⟩ := Finset.mem_filter.1 hp
          obtain ⟨h3, h4⟩ := Finset.mem_filter.1 h1
          exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), (Finset.mem_filter.1 h3).2⟩
        · exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le
  · rw [← Finset.prod_filter_mul_prod_filter_not _ (· ≤ n)]
    have h1 : ∏ x ∈ {x ∈ {x ∈ S0 | ¬ x ≤ 2 * n / 3} | x ≤ n}, f x = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      obtain ⟨_, h4⟩ := Finset.mem_filter.1 h1
      dsimp only [f]
      rw [factorization_centralBinom_of_two_mul_self_lt_three_mul n_large h2 (by omega),
        _root_.pow_zero]
    rw [h1, one_mul]
    refine (Finset.prod_le_prod' fun p _ => hf p).trans ?_
    rw [Finset.prod_const]
    refine pow_right_mono₀ n2_pos (Finset.card_le_card fun x hx => ?_)
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    obtain ⟨h3, _⟩ := Finset.mem_filter.1 h1
    obtain ⟨h5, h6⟩ := Finset.mem_filter.1 h3
    exact Finset.mem_filter.2 ⟨h5, h6, by omega⟩

theorem primeCounting_le (s : ℕ) (hs : 6 ≤ s) : (primeCounting s : ℝ) ≤ s / 3 + 3 := by
  have h := Nat.primeCounting_add_le (a := 6) (k := 6) (by norm_num) le_rfl (s - 6)
  have e : 6 + (s - 6) = s := by omega
  rw [e] at h
  have h6 : primeCounting 6 = 3 := by decide
  have t6 : totient 6 = 2 := by decide
  rw [h6, t6] at h
  have h2 : (((s - 6) / 6 : ℕ) : ℝ) ≤ ((s - 6 : ℕ) : ℝ) / 6 := Nat.cast_div_le
  have h3 : ((s - 6 : ℕ) : ℝ) = (s : ℝ) - 6 := by
    rw [Nat.cast_sub hs]; norm_num
  have h4 : (primeCounting s : ℝ) ≤ 3 + 2 * ((((s - 6) / 6 : ℕ) : ℝ) + 1) := by exact_mod_cast h
  rw [h3] at h2
  linarith

theorem real_ineq {y l L k : ℝ} (hy : 141 ≤ y) (hl1 : 0.6931471803 < l) (hl2 : l < 0.6931471808)
    (hL : L ≤ 2 * (7 * l + y / 128 - 1))
    (h : y ^ 2 * l / 3 < (y / 3 + 4 + k) * L) : y ^ 2 + 1 ≤ 5 * (k - 3) * L := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  rcases le_or_gt L 0 with hL0 | hL0
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y / 3 + 7) (neg_nonneg.2 hL0),
      mul_le_mul_of_nonneg_left hl1.le (sq_nonneg y), mul_nonneg (by linarith : (0 : ℝ) ≤ y - 141) hy0]
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y / 3 + 7) (by linarith : (0 : ℝ) ≤ 2 * (7 * l + y / 128 - 1) - L),
      mul_le_mul_of_nonneg_left hl1.le (sq_nonneg y), mul_nonneg (by linarith : (0 : ℝ) ≤ y - 141) hy0,
      mul_le_mul_of_nonneg_left hl2.le hy0]

theorem upper_card (n : ℕ) (hn : 10000 ≤ n) :
    (2 * (n : ℝ) + 1) ≤ 5 * (((upper n).card : ℝ) - 3) * Real.log (2 * n) := by
  have h1 : 4 ^ n < n * centralBinom n := Nat.four_pow_lt_mul_centralBinom n (by omega)
  have h2 := centralBinom_le n (by omega)
  set k := (upper n).card with hk
  set s := sqrt (2 * n) with hs
  set c := primeCounting s with hc
  have h3 : 4 ^ n < n * (((2 * n) ^ c * 4 ^ (2 * n / 3)) * (2 * n) ^ k) :=
    lt_of_lt_of_le h1 (Nat.mul_le_mul_left n h2)
  have h4 : (4 : ℝ) ^ n < n * (((2 * n) ^ c * 4 ^ (2 * n / 3)) * (2 * n) ^ k) := by
    exact_mod_cast h3
  have hn1 : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have h2n : (0 : ℝ) < 2 * n := by linarith
  have h5 := Real.log_lt_log (by positivity) h4
  rw [Real.log_mul hnpos.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_pow] at h5
  set L := Real.log (2 * n) with hLdef
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [hl4] at h5
  set l := Real.log 2 with hl
  have hl1 : 0.6931471803 < l := Real.log_two_gt_d9
  have hl2 : l < 0.6931471808 := Real.log_two_lt_d9
  set y := Real.sqrt (2 * n) with hy
  have hy2 : y ^ 2 = 2 * n := Real.sq_sqrt h2n.le
  have hy141 : 141 ≤ y := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have hypos : 0 < y := by linarith
  have hsy : (s : ℝ) ≤ y := by
    have := Real.nat_sqrt_le_real_sqrt (a := 2 * n)
    simpa [hs, hy] using this
  have hs6 : 6 ≤ s := by
    rw [hs, Nat.le_sqrt]; omega
  have hcs : (c : ℝ) ≤ s / 3 + 3 := primeCounting_le s hs6
  have hLy : L = 2 * Real.log y := by
    rw [hLdef, ← hy2, Real.log_pow]; norm_num
  have hlogy : Real.log y ≤ 7 * l + y / 128 - 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < y / 128 by positivity)
    rw [Real.log_div hypos.ne' (by norm_num), show (128 : ℝ) = 2 ^ 7 by norm_num,
      Real.log_pow] at h
    push_cast at h
    linarith
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hlogn : Real.log n ≤ L := Real.log_le_log hnpos (by linarith)
  have hdiv : (((2 * n / 3 : ℕ)) : ℝ) ≤ (2 * n : ℝ) / 3 := by
    have := (Nat.cast_div_le : (((2 * n) / 3 : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) / ((3 : ℕ) : ℝ))
    simpa using this
  have hcL : (c : ℝ) * L ≤ (y / 3 + 3) * L := mul_le_mul_of_nonneg_right (by linarith) hL0
  have hdl : (((2 * n / 3 : ℕ)) : ℝ) * (2 * l) ≤ (2 * n : ℝ) / 3 * (2 * l) :=
    mul_le_mul_of_nonneg_right hdiv (by linarith)
  have key : y ^ 2 * l / 3 < (y / 3 + 4 + k) * L := by
    rw [hy2]
    nlinarith
  have := real_ineq hy141 hl1 hl2 (by linarith) key
  rw [hy2] at this
  exact this

theorem S_large (N : ℕ) (hN : 20000 ≤ N) : 1 / (5 * Real.log N) ≤ S N := by
  obtain ⟨n, hn⟩ : ∃ n, n = N / 2 := ⟨_, rfl⟩
  have hn1 : 10000 ≤ n := by omega
  have hU := upper_card n hn1
  set F := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) with hF
  have hsub : upper n ⊆ F ∪ {N - 2, N - 1, N} := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hp
    have h1' := Finset.mem_range.1 h1
    by_cases h4 : p + 3 ≤ N
    · exact Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), h2, by omega, h4⟩)
    · refine Finset.mem_union_right _ ?_
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
  have hcard : (upper n).card ≤ F.card + 3 :=
    (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_le_three _))
  have hcardR : ((upper n).card : ℝ) ≤ (F.card : ℝ) + 3 := by exact_mod_cast hcard
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hS : (F.card : ℝ) / N ≤ S N := by
    have e : (F.card : ℝ) / N = ∑ _p ∈ F, (1 : ℝ) / N := by
      rw [Finset.sum_const, nsmul_eq_mul]; ring
    rw [e]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨h1, h2, _, _⟩ := Finset.mem_filter.1 hp
    have h1' : p ≤ N := by have := Finset.mem_range.1 h1; omega
    exact one_div_le_one_div_of_le (by exact_mod_cast h2.pos) (by exact_mod_cast h1')
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn1
  have h2nN : (2 * (n : ℝ)) ≤ N := by
    have : 2 * n ≤ N := by omega
    exact_mod_cast this
  have hN2n : (N : ℝ) ≤ 2 * n + 1 := by
    have : N ≤ 2 * n + 1 := by omega
    exact_mod_cast this
  have hL0 : 0 < Real.log (2 * n) := Real.log_pos (by linarith)
  have hLN : Real.log (2 * n) ≤ Real.log N := Real.log_le_log (by linarith) h2nN
  have hc0 : (0 : ℝ) ≤ F.card := Nat.cast_nonneg _
  have h1 : 5 * (((upper n).card : ℝ) - 3) * Real.log (2 * n) ≤ 5 * (F.card : ℝ) * Real.log (2 * n) :=
    mul_le_mul_of_nonneg_right (by linarith) hL0.le
  have h2 : 5 * (F.card : ℝ) * Real.log (2 * n) ≤ 5 * (F.card : ℝ) * Real.log N :=
    mul_le_mul_of_nonneg_left hLN (by linarith)
  refine le_trans ?_ hS
  rw [div_le_div_iff₀ (by linarith) hNpos]
  linarith

theorem four_le_log (N : ℕ) (hN : 100 ≤ N) : 4 ≤ Real.log N := by
  have h1 : Real.exp 4 ≤ 100 := by
    have he := Real.exp_one_lt_d9
    have h2 : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h2]
    calc Real.exp 1 ^ 4 ≤ 2.7182818286 ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 4
      _ ≤ 100 := by norm_num
  have h2 : (100 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith

end PrimeCountingLemmas

theorem prime_reciprocal_sum_bound : PrimeRecipSum := by
  intro N hN
  change 1 / (5 * Real.log N) ≤ PrimeCountingLemmas.S N
  by_cases h : N < 20000
  · have h4 := PrimeCountingLemmas.four_le_log N hN
    exact (one_div_le_one_div_of_le (by norm_num) (by linarith)).trans (PrimeCountingLemmas.S_small N hN h)
  · exact PrimeCountingLemmas.S_large N (by omega)

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
