import Mathlib
open Classical

namespace GlobalTheory.PrimeRecip

noncomputable def noSmallDiv (p : ℕ) : ℕ → Bool
  | 0 => true
  | d + 1 => (p < (d + 1) * (d + 1) || d + 1 < 2 || p % (d + 1) != 0) && noSmallDiv p d

noncomputable def sortedB : List ℕ → Bool
  | a :: b :: t => a < b && sortedB (b :: t)
  | _ => true

noncomputable def okIv (a b j c : ℕ) (L : List ℕ) : Bool :=
  (L.all fun p => 2 ≤ p && p < 17161 && noSmallDiv p 130 && b ≤ 2 * p && p + 3 ≤ a && p ≤ c) &&
    sortedB L && 2 ^ j ≤ a && 0 < c && c * 10 ^ 10 ≤ 5 * L.length * j * 6931471803

noncomputable def okAll : ℕ → List (ℕ × ℕ × ℕ × ℕ × List ℕ) → ℕ → Bool
  | lo, [], hi => hi ≤ lo
  | lo, (a, b, j, c, L) :: rest, hi => a ≤ lo && okIv a b j c L && okAll b rest hi

theorem noSmallDiv_spec (p : ℕ) : ∀ D, noSmallDiv p D = true →
    ∀ d, 2 ≤ d → d ≤ D → d * d ≤ p → p % d ≠ 0 := by
  intro D
  induction D with
  | zero => intro _ d h2 hD; omega
  | succ D ih =>
    intro h d h2 hD hdd
    simp only [noSmallDiv, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge d (D + 1) with hlt | hge
    · exact ih h.2 d h2 (by omega) hdd
    · have hd : d = D + 1 := by omega
      subst hd
      have h1 := h.1
      simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h1
      rcases h1 with (h1 | h1) | h1
      · omega
      · omega
      · exact h1

theorem prime_of_check {p : ℕ} (h2 : 2 ≤ p) (hp : p < 17161) (h : noSmallDiv p 130 = true) :
    p.Prime := by
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, fun m hm hms hdvd => ?_⟩
  have hmm : m * m ≤ p := Nat.le_sqrt.1 hms
  have hm130 : m ≤ 130 := by nlinarith
  exact noSmallDiv_spec p 130 h m hm hm130 hmm (Nat.dvd_iff_mod_eq_zero.1 hdvd)

theorem sortedB_pairwise : ∀ L : List ℕ, sortedB L = true → L.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: t, h => by
    simp only [sortedB, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := sortedB_pairwise (b :: t) h.2
    refine List.pairwise_cons.2 ⟨fun x hx => ?_, ih⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact h.1.trans (List.rel_of_pairwise_cons ih hx)

theorem okIv_sound {a b j c : ℕ} {L : List ℕ} (h : okIv a b j c L = true) (N : ℕ) (haN : a ≤ N)
    (hNb : N < b) :
    1 / (5 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p := by
  simp only [okIv, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hall, hsort⟩, hj⟩, hc0⟩, hk⟩ := h
  have hnd : L.Nodup := (sortedB_pairwise L hsort).imp (fun h => ne_of_lt h)
  have hcard : L.toFinset.card = L.length := List.toFinset_card_of_nodup hnd
  have hsub : L.toFinset ⊆
      (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) := by
    intro p hp
    rw [List.mem_toFinset] at hp
    obtain ⟨⟨⟨⟨⟨h2, h3⟩, h4⟩, h5⟩, h6⟩, -⟩ := hall p hp
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, prime_of_check h2 h3 h4, by omega, by omega⟩
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc0
  have hkR : (c : ℝ) * 10 ^ 10 ≤ 5 * L.length * j * 6931471803 := by exact_mod_cast hk
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; simp at hk; omega
    · exact h0
  have h2j : 2 ≤ N := by
    have : 2 ^ 1 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
    omega
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast h2j
  have hlogN : (j : ℝ) * Real.log 2 ≤ Real.log N := by
    have h2jR : ((2 : ℝ)) ^ j ≤ N := by exact_mod_cast (hj.trans haN)
    have := Real.log_le_log (by positivity) h2jR
    rwa [Real.log_pow] at this
  have hl2 := Real.log_two_gt_d9
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  calc 1 / (5 * Real.log N) ≤ (L.length : ℝ) * (1 / c) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) hcR]
        have e1 : (L.length : ℝ) * (j * 0.6931471803) ≤ L.length * (j * Real.log 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl2.le (by positivity))
            (by positivity)
        have e2 : (L.length : ℝ) * (j * Real.log 2) ≤ L.length * Real.log N :=
          mul_le_mul_of_nonneg_left hlogN (by positivity)
        nlinarith
    _ = ∑ _p ∈ L.toFinset, (1 : ℝ) / c := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
    _ ≤ ∑ p ∈ L.toFinset, (1 : ℝ) / p := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [List.mem_toFinset] at hp
        obtain ⟨⟨⟨⟨⟨h2, -⟩, -⟩, -⟩, -⟩, h7⟩ := hall p hp
        have : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
        exact one_div_le_one_div_of_le this (by exact_mod_cast h7)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

theorem okAll_sound : ∀ (T : List (ℕ × ℕ × ℕ × ℕ × List ℕ)) (lo hi : ℕ), okAll lo T hi = true →
    ∀ N, lo ≤ N → N < hi → 1 / (5 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p
  | [], lo, hi, h, N, h1, h2 => by simp [okAll] at h; omega
  | (a, b, j, c, L) :: rest, lo, hi, h, N, h1, h2 => by
    simp only [okAll, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hal, hiv⟩, hrest⟩ := h
    by_cases hNb : N < b
    · exact okIv_sound hiv N (by omega) hNb
    · exact okAll_sound rest b hi hrest N (by omega) h2

theorem three_mul_primeCounting_le (s : ℕ) (hs : 6 ≤ s) : 3 * Nat.primeCounting s ≤ s + 9 := by
  have h := Nat.primeCounting_add_le (a := 6) (k := 6) (by norm_num) le_rfl (s - 6)
  rw [show 6 + (s - 6) = s by omega] at h
  have h6 : Nat.primeCounting 6 = 3 := by decide
  have ht : Nat.totient 6 = 2 := by decide
  rw [h6, ht] at h
  omega

theorem centralBinom_le_pow_primeCounting (n : ℕ) (n_large : 2 < n) :
    n.centralBinom ≤ (2 * n) ^ Nat.primeCounting (Nat.sqrt (2 * n)) * 4 ^ (2 * n / 3) *
      (2 * n) ^ ((Finset.range (2 * n + 1)).filter (fun p => p.Prime ∧ n < p)).card := by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt n_large
  have n2_pos : 1 ≤ 2 * n := mul_pos (zero_lt_two' ℕ) n_pos
  let S := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
  let T := (Finset.range (2 * n + 1)).filter (fun p => p.Prime ∧ n < p)
  let f : ℕ → ℕ := fun x => x ^ n.centralBinom.factorization x
  have hf : ∀ p, f p ≤ 2 * n := fun p => Nat.pow_factorization_choose_le (mul_pos two_pos n_pos)
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hx hy
    have h1 := Finset.mem_range.1 (Finset.mem_filter.1 hx).1
    have h2 := (Finset.mem_filter.1 hy).2.2
    omega
  have key : n.centralBinom = (∏ x ∈ S, f x) * ∏ x ∈ T, f x := by
    rw [← Finset.prod_union hdisj]
    refine (Eq.trans ?_ n.prod_pow_factorization_centralBinom).symm
    apply Finset.prod_subset
    · intro x hx
      rcases Finset.mem_union.1 hx with h | h
      · have h1 := Finset.mem_range.1 (Finset.mem_filter.1 h).1
        rw [Finset.mem_range]; omega
      · exact (Finset.mem_filter.1 h).1
    intro x hx h2x
    by_cases hp : x.Prime
    · have h1 : ¬ x < 2 * n / 3 + 1 := fun h => h2x (Finset.mem_union.2 (Or.inl
        (Finset.mem_filter.2 ⟨Finset.mem_range.2 h, hp⟩)))
      have h2 : ¬ n < x := fun h => h2x (Finset.mem_union.2 (Or.inr
        (Finset.mem_filter.2 ⟨hx, hp, h⟩)))
      have h3 : 2 * n < 3 * x := by omega
      simp only [f]
      rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul n_large (not_lt.1 h2) h3,
        Nat.pow_zero]
    · simp only [f]
      rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom hp, Nat.pow_zero]
  rw [key]
  apply mul_le_mul'
  · rw [← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt (2 * n))]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod' fun p _ => hf p).trans ?_
      rw [Finset.prod_const]
      refine pow_right_mono₀ n2_pos ?_
      rw [← Nat.primesLE_card_eq_primeCounting]
      refine Finset.card_le_card fun x hx => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      exact Nat.mem_primesLE.2 ⟨h2, (Finset.mem_filter.1 h1).2⟩
    · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
      refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
        refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp <| not_le.1 h2)
      refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
      exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le
  · refine (Finset.prod_le_prod' fun p _ => hf p).trans ?_
    rw [Finset.prod_const]

theorem inv_five_log_le_sum_inv_primes_of_large (N : ℕ) (hN : 16900 ≤ N) :
    1 / (5 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p := by
  set U := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) with hU
  obtain ⟨n, hn⟩ : ∃ n, n = N / 2 := ⟨_, rfl⟩
  set T := (Finset.range (2 * n + 1)).filter (fun p => p.Prime ∧ n < p) with hT
  have hcard : T.card ≤ U.card + 3 := by
    have hsub : T ⊆ U ∪ {N - 2, N - 1, N} := by
      intro x hx
      obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hx
      rw [Finset.mem_range] at h1
      by_cases h : x + 3 ≤ N
      · exact Finset.mem_union.2 (Or.inl (Finset.mem_filter.2
          ⟨Finset.mem_range.2 (by omega), h2, by omega, h⟩))
      · refine Finset.mem_union.2 (Or.inr ?_)
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    exact Nat.add_le_add_left Finset.card_le_three _
  have h1 := Nat.four_pow_lt_mul_centralBinom n (by omega)
  have h2 := centralBinom_le_pow_primeCounting n (by omega)
  rw [← hT] at h2
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt N := ⟨_, rfl⟩
  have hs1 : s * s ≤ N := hs ▸ Nat.sqrt_le N
  have hs2 : N < (s + 1) * (s + 1) := hs ▸ Nat.lt_succ_sqrt N
  have hs3 : 130 ≤ s := by
    by_contra h
    have : s + 1 ≤ 130 := by omega
    have := Nat.mul_le_mul this this
    omega
  obtain ⟨K, hK⟩ : ∃ K, K = Nat.primeCounting (Nat.sqrt (2 * n)) := ⟨_, rfl⟩
  rw [← hK] at h2
  have hK3 : 3 * K ≤ s + 9 := by
    have a : K ≤ Nat.primeCounting s :=
      hK ▸ Nat.monotone_primeCounting (hs ▸ Nat.sqrt_le_sqrt (by omega))
    have b := three_mul_primeCounting_le s (by omega)
    omega
  obtain ⟨m, hm⟩ : ∃ m, m = n - 2 * n / 3 := ⟨_, rfl⟩
  have h3 : 4 ^ m ≤ N ^ (K + U.card + 4) := by
    have hNpos : 1 ≤ N := by omega
    have e : 4 ^ n = 4 ^ m * 4 ^ (2 * n / 3) := by
      rw [← pow_add]; congr 1; omega
    have a1 : (2 * n) ^ K ≤ N ^ K := Nat.pow_le_pow_left (by omega) _
    have a2 : (2 * n) ^ T.card ≤ N ^ (U.card + 3) :=
      (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right hNpos hcard)
    have a3 : 4 ^ m * 4 ^ (2 * n / 3) ≤ N ^ (K + U.card + 4) * 4 ^ (2 * n / 3) := by
      rw [← e]
      calc 4 ^ n ≤ n * n.centralBinom := h1.le
        _ ≤ N * (N ^ K * 4 ^ (2 * n / 3) * N ^ (U.card + 3)) :=
          Nat.mul_le_mul (by omega) (h2.trans (Nat.mul_le_mul (Nat.mul_le_mul_right _ a1) a2))
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right a3 (by positivity)
  have hNR : (16900 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have h4 : (m : ℝ) * Real.log 4 ≤ (K + U.card + 4) * Real.log N := by
    have : ((4 : ℝ)) ^ m ≤ (N : ℝ) ^ (K + U.card + 4) := by exact_mod_cast h3
    have := Real.log_le_log (by positivity) this
    rw [Real.log_pow, Real.log_pow] at this
    exact_mod_cast this
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hmR : (N : ℝ) ≤ 6 * m + 1 := by
    have : N ≤ 6 * m + 1 := by omega
    exact_mod_cast this
  have hsR : (130 : ℝ) ≤ s := by exact_mod_cast hs3
  have hs1R : (s : ℝ) * s ≤ N := by exact_mod_cast hs1
  have hs2R : (N : ℝ) ≤ (s + 1) * (s + 1) := by exact_mod_cast hs2.le
  have hK3R : 3 * (K : ℝ) ≤ s + 9 := by exact_mod_cast hK3
  have hLle : Real.log N ≤ (s + 1) / 64 + 7.70407 := by
    have b1 : Real.log N ≤ 2 * Real.log (s + 1) := by
      have := Real.log_le_log (by linarith) hs2R
      rw [Real.log_mul (by linarith) (by linarith)] at this
      linarith
    have b2 : Real.log ((s + 1) / 2 ^ 7) ≤ (s + 1) / 2 ^ 7 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by linarith) (by norm_num), Real.log_pow] at b2
    push_cast at b2
    linarith
  have h5 : (N : ℝ) ≤ U.card * (5 * Real.log N) := by
    have c1 : ((s : ℝ) + 21) * Real.log N ≤ (s + 21) * ((s + 1) / 64 + 7.70407) :=
      mul_le_mul_of_nonneg_left hLle (by linarith)
    have c2 : (m : ℝ) * 1.386294 ≤ m * Real.log 4 :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    have c3 : 130 * (s : ℝ) ≤ s * s := mul_le_mul_of_nonneg_right hsR (by linarith)
    have c4 : 3 * (K : ℝ) * Real.log N ≤ (s + 9) * Real.log N :=
      mul_le_mul_of_nonneg_right hK3R hL.le
    nlinarith
  calc 1 / (5 * Real.log N) ≤ (U.card : ℝ) * (1 / N) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by linarith)]
        linarith
    _ = ∑ _p ∈ U, (1 : ℝ) / N := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨-, hp1, -, hp2⟩ := Finset.mem_filter.1 hp
        have : (0 : ℝ) < p := by exact_mod_cast hp1.pos
        have h' : (p : ℝ) ≤ N := by exact_mod_cast (by omega : p ≤ N)
        exact one_div_le_one_div_of_le this h'

def table : List (ℕ × ℕ × ℕ × ℕ × List ℕ) := [
  (100, 146, 6, 97, [73, 79, 83, 89, 97]),
  (146, 218, 7, 139, [109, 113, 127, 131, 137, 139]),
  (218, 334, 7, 211, [167, 173, 179, 181, 191, 193, 197, 199, 211]),
  (334, 526, 8, 331, [263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331]),
  (526, 862, 9, 523, [431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523]),
  (862, 1346, 9, 859, [673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859]),
  (1346, 2126, 10, 1327, [1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327]),
  (2126, 3386, 11, 2113, [1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113]),
  (3386, 5354, 11, 3373, [2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373]),
  (5354, 8462, 12, 5351, [4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351]),
  (8462, 13522, 13, 8447, [6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431, 8443, 8447]),
  (13522, 16900, 13, 13513, [10667, 10687, 10691, 10709, 10711, 10723, 10729, 10733, 10739, 10753, 10771, 10781, 10789, 10799, 10831, 10837, 10847, 10853, 10859, 10861, 10867, 10883, 10889, 10891, 10903, 10909, 10937, 10939, 10949, 10957, 10973, 10979, 10987, 10993, 11003, 11027, 11047, 11057, 11059, 11069, 11071, 11083, 11087, 11093, 11113, 11117, 11119, 11131, 11149, 11159, 11161, 11171, 11173, 11177, 11197, 11213, 11239, 11243, 11251, 11257, 11261, 11273, 11279, 11287, 11299, 11311, 11317, 11321, 11329, 11351, 11353, 11369, 11383, 11393, 11399, 11411, 11423, 11437, 11443, 11447, 11467, 11471, 11483, 11489, 11491, 11497, 11503, 11519, 11527, 11549, 11551, 11579, 11587, 11593, 11597, 11617, 11621, 11633, 11657, 11677, 11681, 11689, 11699, 11701, 11717, 11719, 11731, 11743, 11777, 11779, 11783, 11789, 11801, 11807, 11813, 11821, 11827, 11831, 11833, 11839, 11863, 11867, 11887, 11897, 11903, 11909, 11923, 11927, 11933, 11939, 11941, 11953, 11959, 11969, 11971, 11981, 11987, 12007, 12011, 12037, 12041, 12043, 12049, 12071, 12073, 12097, 12101, 12107, 12109, 12113, 12119, 12143, 12149, 12157, 12161, 12163, 12197, 12203, 12211, 12227, 12239, 12241, 12251, 12253, 12263, 12269, 12277, 12281, 12289, 12301, 12323, 12329, 12343, 12347, 12373, 12377, 12379, 12391, 12401, 12409, 12413, 12421, 12433, 12437, 12451, 12457, 12473, 12479, 12487, 12491, 12497, 12503, 12511, 12517, 12527, 12539, 12541, 12547, 12553, 12569, 12577, 12583, 12589, 12601, 12611, 12613, 12619, 12637, 12641, 12647, 12653, 12659, 12671, 12689, 12697, 12703, 12713, 12721, 12739, 12743, 12757, 12763, 12781, 12791, 12799, 12809, 12821, 12823, 12829, 12841, 12853, 12889, 12893, 12899, 12907, 12911, 12917, 12919, 12923, 12941, 12953, 12959, 12967, 12973, 12979, 12983, 13001, 13003, 13007, 13009, 13033, 13037, 13043, 13049, 13063, 13093, 13099, 13103, 13109, 13121, 13127, 13147, 13151, 13159, 13163, 13171, 13177, 13183, 13187, 13217, 13219, 13229, 13241, 13249, 13259, 13267, 13291, 13297, 13309, 13313, 13327, 13331, 13337, 13339, 13367, 13381, 13397, 13399, 13411, 13417, 13421, 13441, 13451, 13457, 13463, 13469, 13477, 13487, 13499, 13513])]

theorem table_ok : okAll 100 table 16900 = true := by decide +kernel

theorem inv_five_log_le_sum_inv_primes :
    ∀ N : ℕ, 100 ≤ N → 1 / (5 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p := by
  intro N hN
  by_cases h : N < 16900
  · exact okAll_sound table 100 16900 table_ok N hN h
  · exact inv_five_log_le_sum_inv_primes_of_large N (by omega)

end GlobalTheory.PrimeRecip
