import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ReducedBasisStatement

namespace ReciprocityTheory.ChartRestriction.G.H1

lemma primeLogSum_log_factorial_le {N : ℕ} (hN : 1 ≤ N) :
    Real.log ((N.factorial : ℕ) : ℝ) ≤ ((N : ℝ) + 1) * Real.log N - N + 1 := by
  induction N, hN using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ n hn ih =>
    have hx : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hk : ((n:ℝ) + 1) * (Real.log n - Real.log ((n:ℝ) + 1)) ≤ -1 := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (n:ℝ) / ((n:ℝ) + 1) from div_pos hx (by positivity))
      rw [Real.log_div hx.ne' (by positivity)] at h
      have e : ((n:ℝ) + 1) * ((n:ℝ) / ((n:ℝ) + 1) - 1) = -1 := by
        first
        | (field_simp; ring)
        | field_simp
      nlinarith [mul_le_mul_of_nonneg_left h (show (0:ℝ) ≤ (n:ℝ) + 1 by positivity)]
    rw [Nat.factorial_succ]
    push_cast
    rw [Real.log_mul (by positivity) (by exact_mod_cast (Nat.factorial_ne_zero n))]
    nlinarith [ih, hk]

lemma primeLogSum_div_le_factorization (N p : ℕ) (hp : p.Prime) (hpN : p ≤ N) :
    N / p ≤ (N.factorial).factorization p := by
  have hlog : 0 < Nat.log p N := by
    first
    | exact Nat.log_pos hp.one_lt hpN
    | exact Nat.log_pos_iff.mpr ⟨hpN, hp.one_lt⟩
    | exact Nat.log_pos_iff.mpr ⟨hp.one_lt, hpN⟩
    | exact Nat.log_pos hpN hp.one_lt
  haveI := Fact.mk hp
  rw [Nat.factorization_def _ hp, padicValNat_factorial (Nat.lt_add_one (Nat.log p N))]
  have h1 : 1 ∈ Finset.Ico 1 (Nat.log p N + 1) := by
    rw [Finset.mem_Ico]
    omega
  calc N / p = N / p ^ 1 := by rw [pow_one]
    _ ≤ ∑ i ∈ Finset.Ico 1 (Nat.log p N + 1), N / p ^ i :=
      Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) h1

lemma primeLogSum_log_factorial_eq (N : ℕ) :
    Real.log ((N.factorial : ℕ) : ℝ) = ∑ p ∈ (Finset.Iic N).filter Nat.Prime,
      ((N.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    have hp' : p.Prime ∧ p ∣ N.factorial := by
      first
      | (rw [Nat.support_factorization] at hp; exact ⟨Nat.prime_of_mem_primeFactors hp, Nat.dvd_of_mem_primeFactors hp⟩)
      | exact ⟨Nat.prime_of_mem_factorization hp, Nat.dvd_of_mem_factorization hp⟩
    rw [Finset.mem_filter, Finset.mem_Iic]
    exact ⟨(Nat.Prime.dvd_factorial hp'.1).mp hp'.2, hp'.1⟩
  · intro i _
    simp

lemma primeLogSum_point (N p : ℕ) (hp : p.Prime) (hpN : p ≤ N) :
    (N : ℝ) * (Real.log p / p) ≤
      ((N.factorial.factorization p : ℕ) : ℝ) * Real.log p + Real.log p := by
  have hv := primeLogSum_div_le_factorization N p hp hpN
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hpp : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hnat : N ≤ N.factorial.factorization p * p + p := by
    have h1 := Nat.div_add_mod N p
    have h2 := Nat.mod_lt N hp.pos
    have h3 : N / p * p ≤ N.factorial.factorization p * p := by
      first
      | exact Nat.mul_le_mul_right p hv
      | exact Nat.mul_le_mul_right hv
      | nlinarith
    linarith
  have hN : (N:ℝ) ≤ ((N.factorial.factorization p : ℕ) : ℝ) * p + p := by exact_mod_cast hnat
  rw [← mul_div_assoc]
  first
  | rw [div_le_iff₀ hpp]
  | rw [div_le_iff hpp]
  nlinarith [mul_le_mul_of_nonneg_right hN hlog]

lemma primeLogSum_theta (N : ℕ) :
    ∑ p ∈ (Finset.Iic N).filter Nat.Prime, Real.log p ≤ Real.log 4 * N := by
  have hA : (Finset.Iic N).filter Nat.Prime = (Finset.range (N + 1)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, h2⟩
  have hprod : ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, p ≤ 4 ^ N := by
    first
    | exact primorial_le_4_pow N
    | exact Nat.primorial_le_4_pow N
  have hne : ∀ p ∈ (Finset.range (N + 1)).filter Nat.Prime, ((p : ℕ) : ℝ) ≠ 0 :=
    fun p hp => Nat.cast_ne_zero.mpr (Finset.mem_filter.mp hp).2.ne_zero
  have hpos : (0:ℝ) < ((∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, p : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos)
  rw [hA]
  calc ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p
      = Real.log (∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, ((p : ℕ) : ℝ)) :=
        by
          first
          | exact (Real.log_prod hne).symm
          | exact (Real.log_prod _ _ hne).symm
    _ = Real.log ((∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, p : ℕ) : ℝ) := by
        rw [Nat.cast_prod]
    _ ≤ Real.log ((4 ^ N : ℕ) : ℝ) := by
        first
        | exact Real.log_le_log hpos (by exact_mod_cast hprod)
        | exact Real.log_le_log_of_le hpos (by exact_mod_cast hprod)
    _ = Real.log 4 * N := by
        push_cast
        rw [Real.log_pow]
        ring

lemma primeLogSum_f_nonneg (n : ℕ) : 0 ≤ Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · have h1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    apply div_nonneg (Real.log_nonneg h1)
    exact mul_nonneg (by linarith) (by linarith)

lemma primeLogSum_g_nonneg (n : ℕ) : 0 ≤ Real.log n / ((n : ℝ) - 1) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · have h1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    apply div_nonneg (Real.log_nonneg h1)
    linarith

lemma primeLogSum_log_le (p k : ℕ) (hp : 0 < p) (hk : p ≤ 2 ^ k) :
    Real.log (p : ℝ) ≤ (k : ℝ) * Real.log 2 := by
  have h1 : (0:ℝ) < p := by exact_mod_cast hp
  have h2 : (p:ℝ) ≤ (2:ℝ) ^ k := by exact_mod_cast hk
  calc Real.log (p : ℝ) ≤ Real.log ((2:ℝ) ^ k) := by
        first
        | exact Real.log_le_log h1 h2
        | exact Real.log_le_log_of_le h1 h2
    _ = (k : ℝ) * Real.log 2 := by
        first
        | exact Real.log_pow 2 k
        | exact Real.log_pow k 2

lemma primeLogSum_tele (m : ℕ) (hm : 2 ≤ m) :
    Real.log ((m + 1 : ℕ) : ℝ) / (((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) - 1)) ≤
      (Real.log (m : ℝ) + 1) / ((m : ℝ) - 1) -
        (Real.log ((m + 1 : ℕ) : ℝ) + 1) / (((m + 1 : ℕ) : ℝ) - 1) := by
  have hx2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have e1 : ((m + 1 : ℕ) : ℝ) = (m:ℝ) + 1 := by push_cast; ring
  have e2 : (m:ℝ) + 1 - 1 = m := by ring
  rw [e1, e2]
  have hx0 : (0:ℝ) < m := by linarith
  have hl : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg (by linarith)
  have hLl : Real.log (m:ℝ) ≤ Real.log ((m:ℝ) + 1) := by
    first
    | exact Real.log_le_log hx0 (by linarith)
    | exact Real.log_le_log_of_le hx0 (by linarith)
  have hk : (m:ℝ) * (Real.log ((m:ℝ) + 1) - Real.log m) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((m:ℝ) + 1) / m from div_pos (by linarith) hx0)
    rw [Real.log_div (by positivity) hx0.ne'] at h
    have e : (m:ℝ) * (((m:ℝ) + 1) / m - 1) = 1 := by
      first
      | (field_simp; ring)
      | field_simp
    calc (m:ℝ) * (Real.log ((m:ℝ) + 1) - Real.log m) ≤ (m:ℝ) * (((m:ℝ) + 1) / m - 1) :=
          mul_le_mul_of_nonneg_left h hx0.le
      _ = 1 := e
  have hm1 : (0:ℝ) < (m:ℝ) - 1 := by linarith
  have hA : (m:ℝ) - 1 ≠ 0 := hm1.ne'
  have hB : (m:ℝ) ≠ 0 := hx0.ne'
  have hC : (m:ℝ) + 1 ≠ 0 := by positivity
  have hden : (0:ℝ) < ((m:ℝ) - 1) * m * ((m:ℝ) + 1) := mul_pos (mul_pos hm1 hx0) (by linarith)
  have e : (Real.log (m:ℝ) + 1) / ((m:ℝ) - 1) - (Real.log ((m:ℝ) + 1) + 1) / m
      - Real.log ((m:ℝ) + 1) / (((m:ℝ) + 1) * m)
      = ((Real.log (m:ℝ) + 1) * m * ((m:ℝ) + 1) - (Real.log ((m:ℝ) + 1) + 1) * ((m:ℝ) - 1) * ((m:ℝ) + 1)
          - Real.log ((m:ℝ) + 1) * ((m:ℝ) - 1)) / (((m:ℝ) - 1) * m * ((m:ℝ) + 1)) := by
    first
    | (field_simp; ring)
    | (rw [eq_div_iff hden.ne']; field_simp)
    | (rw [eq_div_iff hden.ne']; field_simp; ring)
  have hnum : 0 ≤ (Real.log (m:ℝ) + 1) * m * ((m:ℝ) + 1)
      - (Real.log ((m:ℝ) + 1) + 1) * ((m:ℝ) - 1) * ((m:ℝ) + 1)
      - Real.log ((m:ℝ) + 1) * ((m:ℝ) - 1) := by
    nlinarith [mul_le_mul_of_nonneg_right hk (show (0:ℝ) ≤ (m:ℝ) + 1 by linarith)]
  have := div_nonneg hnum hden.le
  linarith

lemma sum_Icc_log_div_le_sub (k : ℕ) :
    ∑ n ∈ Finset.Icc 31 (30 + k), Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) ≤
      (Real.log ((30 : ℕ) : ℝ) + 1) / (((30 : ℕ) : ℝ) - 1) -
        (Real.log ((30 + k : ℕ) : ℝ) + 1) / (((30 + k : ℕ) : ℝ) - 1) := by
  induction k with
  | zero =>
    rw [Finset.Icc_eq_empty (by norm_num)]
    simp
  | succ k ih =>
    rw [← Nat.add_assoc, Finset.sum_Icc_succ_top (by omega)]
    have ht := primeLogSum_tele (30 + k) (by omega)
    linarith

lemma primeLogSum_tail (N : ℕ) :
    ∑ n ∈ Finset.Icc 31 N, Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) ≤
      (5 * Real.log 2 + 1) / 29 := by
  by_cases hN : N ≤ 30
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    exact div_nonneg (by linarith [Real.log_pos (by norm_num : (1:ℝ) < 2)]) (by norm_num)
  · obtain ⟨k, rfl⟩ : ∃ k, N = 30 + k := ⟨N - 30, by omega⟩
    have h1 := sum_Icc_log_div_le_sub k
    have h2 : 0 ≤ (Real.log ((30 + k : ℕ) : ℝ) + 1) / (((30 + k : ℕ) : ℝ) - 1) := by
      have h30 : (30:ℝ) ≤ ((30 + k : ℕ) : ℝ) := by
        push_cast
        linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
      apply div_nonneg
      · linarith [Real.log_nonneg (show (1:ℝ) ≤ ((30 + k : ℕ) : ℝ) by linarith)]
      · linarith
    have h3 : Real.log ((30 : ℕ) : ℝ) ≤ 5 * Real.log 2 := by
      have := primeLogSum_log_le 30 5 (by norm_num) (by norm_num)
      exact_mod_cast this
    have h4 : (Real.log ((30 : ℕ) : ℝ) + 1) / (((30 : ℕ) : ℝ) - 1) ≤ (5 * Real.log 2 + 1) / 29 := by
      have e : (((30 : ℕ) : ℝ) - 1) = 29 := by norm_num
      have h5 : Real.log ((30 : ℕ) : ℝ) + 1 ≤ 5 * Real.log 2 + 1 := add_le_add h3 le_rfl
      rw [e]
      first
      | exact div_le_div_of_nonneg_right h5 (by norm_num)
      | exact (div_le_div_iff_of_pos_right (by norm_num)).mpr h5
      | exact (div_le_div_right (by norm_num)).mpr h5
      | gcongr
    exact le_trans h1 (le_trans (sub_le_self _ h2) h4)

lemma primeLogSum_small :
    ∑ p ∈ (Finset.Iic 30).filter Nat.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤
      Real.log 2 * (1 / 2 + 2 / 6 + 3 / 20 + 3 / 42 + 4 / 110 + 4 / 156 + 5 / 272 + 5 / 342 +
        5 / 506 + 5 / 812) := by
  rw [Finset.sum_filter]
  have hI : Finset.Iic 30 = Finset.range 31 := by
    ext x
    simp only [Finset.mem_Iic, Finset.mem_range]
    omega
  rw [hI]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have b3 : Real.log 3 ≤ 2 * Real.log 2 := by
    have := primeLogSum_log_le 3 2 (by norm_num) (by norm_num)
    exact_mod_cast this
  have b5 : Real.log 5 ≤ 3 * Real.log 2 := by
    have := primeLogSum_log_le 5 3 (by norm_num) (by norm_num)
    exact_mod_cast this
  have b7 : Real.log 7 ≤ 3 * Real.log 2 := by
    have := primeLogSum_log_le 7 3 (by norm_num) (by norm_num)
    exact_mod_cast this
  have b11 : Real.log 11 ≤ 4 * Real.log 2 := by
    have := primeLogSum_log_le 11 4 (by norm_num) (by norm_num)
    exact_mod_cast this
  have b13 : Real.log 13 ≤ 4 * Real.log 2 := by
    have := primeLogSum_log_le 13 4 (by norm_num) (by norm_num)
    exact_mod_cast this
  have b17 : Real.log 17 ≤ 5 * Real.log 2 := by
    have := primeLogSum_log_le 17 5 (by norm_num) (by norm_num)
    exact_mod_cast this
  have b19 : Real.log 19 ≤ 5 * Real.log 2 := by
    have := primeLogSum_log_le 19 5 (by norm_num) (by norm_num)
    exact_mod_cast this
  have b23 : Real.log 23 ≤ 5 * Real.log 2 := by
    have := primeLogSum_log_le 23 5 (by norm_num) (by norm_num)
    exact_mod_cast this
  have b29 : Real.log 29 ≤ 5 * Real.log 2 := by
    have := primeLogSum_log_le 29 5 (by norm_num) (by norm_num)
    exact_mod_cast this
  norm_num
  linarith

lemma primeLogSum_nat (N : ℕ) (hN : 1 ≤ N) :
    ∑ p ∈ (Finset.Iic N).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) ≤ Real.log N + 2.2 := by
  rcases (show N = 1 ∨ 2 ≤ N by omega) with h1 | hN2
  · subst h1
    have h0 : ∑ p ∈ (Finset.Iic 1).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      have hp3 := Finset.mem_Iic.mp hp1
      exact absurd hp2.two_le (by omega)
    rw [h0]
    norm_num
  · have hsplit : ∑ p ∈ (Finset.Iic N).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) =
        ∑ p ∈ (Finset.Iic N).filter Nat.Prime, Real.log p / (p : ℝ) +
          ∑ p ∈ (Finset.Iic N).filter Nat.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
      have h0 : (p:ℝ) ≠ 0 := (show (0:ℝ) < p by linarith).ne'
      have h1 : (p:ℝ) - 1 ≠ 0 := (show (0:ℝ) < (p:ℝ) - 1 by linarith).ne'
      first
      | (field_simp; ring)
      | field_simp
    have hX : (N:ℝ) * ∑ p ∈ (Finset.Iic N).filter Nat.Prime, Real.log p / (p : ℝ) ≤
        ((N:ℝ) + 1) * Real.log N - N + 1 + Real.log 4 * N := by
      rw [Finset.mul_sum]
      calc ∑ p ∈ (Finset.Iic N).filter Nat.Prime, (N:ℝ) * (Real.log p / (p : ℝ))
          ≤ ∑ p ∈ (Finset.Iic N).filter Nat.Prime,
              (((N.factorial.factorization p : ℕ) : ℝ) * Real.log p + Real.log p) := by
            apply Finset.sum_le_sum
            intro p hp
            obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
            exact primeLogSum_point N p hp2 (Finset.mem_Iic.mp hp1)
        _ = Real.log ((N.factorial : ℕ) : ℝ) + ∑ p ∈ (Finset.Iic N).filter Nat.Prime, Real.log p := by
            rw [Finset.sum_add_distrib, primeLogSum_log_factorial_eq]
        _ ≤ ((N:ℝ) + 1) * Real.log N - N + 1 + Real.log 4 * N := by
            linarith [primeLogSum_log_factorial_le (show 1 ≤ N by omega), primeLogSum_theta N]
    have hS2 : ∑ p ∈ (Finset.Iic N).filter Nat.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤
        Real.log 2 * (1 / 2 + 2 / 6 + 3 / 20 + 3 / 42 + 4 / 110 + 4 / 156 + 5 / 272 + 5 / 342 +
          5 / 506 + 5 / 812) + (5 * Real.log 2 + 1) / 29 := by
      have hsub : (Finset.Iic N).filter Nat.Prime ⊆
          (Finset.Iic 30).filter Nat.Prime ∪ Finset.Icc 31 N := by
        intro p hp
        obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
        have hpN := Finset.mem_Iic.mp hp1
        rw [Finset.mem_union]
        by_cases h : p ≤ 30
        · left
          exact Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr h, hp2⟩
        · right
          exact Finset.mem_Icc.mpr ⟨by omega, hpN⟩
      have hdisj : Disjoint ((Finset.Iic 30).filter Nat.Prime) (Finset.Icc 31 N) := by
        rw [Finset.disjoint_left]
        intro p h1 h2
        have h3 := Finset.mem_Iic.mp (Finset.mem_filter.mp h1).1
        have h4 := (Finset.mem_Icc.mp h2).1
        omega
      calc ∑ p ∈ (Finset.Iic N).filter Nat.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))
          ≤ ∑ p ∈ (Finset.Iic 30).filter Nat.Prime ∪ Finset.Icc 31 N,
              Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => primeLogSum_f_nonneg i)
        _ = ∑ p ∈ (Finset.Iic 30).filter Nat.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) +
              ∑ p ∈ Finset.Icc 31 N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) :=
            Finset.sum_union hdisj
        _ ≤ _ := add_le_add primeLogSum_small (primeLogSum_tail N)
    rw [hsplit]
    have hx2 : (2:ℝ) ≤ N := by exact_mod_cast hN2
    have hlogN : Real.log N ≤ Real.log 2 + (N:ℝ) / 2 - 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (N:ℝ) / 2 by linarith)
      rw [Real.log_div (show (0:ℝ) < N by linarith).ne' (by norm_num)] at h
      linarith
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [hlog4] at hX
    have hL := Real.log_two_lt_d9
    have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hS2' := mul_le_mul_of_nonneg_left hS2 (show (0:ℝ) ≤ N by linarith)
    have hLx := mul_le_mul_of_nonneg_right hL.le (show (0:ℝ) ≤ N by linarith)
    refine le_of_mul_le_mul_left ?_ (show (0:ℝ) < N by linarith)
    first
    | linarith
    | nlinarith [hX, hS2', hlogN, hLx, hL, hL0]

end ReciprocityTheory.ChartRestriction.G.H1
