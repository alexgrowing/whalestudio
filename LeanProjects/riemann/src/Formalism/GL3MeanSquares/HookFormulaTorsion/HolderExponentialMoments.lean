import Mathlib
import Formalism.GL3MeanSquares.RankMulPowThreeHalvesLeFourthPower

namespace Formalism.HermitianLattices.GenusMassVolumes

open Finset

private lemma exponential_moment_pos {ι : Type} [Fintype ι] (P y : ι → ℝ) (hP : ∀ j, 0 ≤ P j) (h1 : ∑ j, P j = 1)
    (t : ℝ) : 0 < ∑ j, P j * Real.exp (t * y j) := by
  have hne : ∃ j, 0 < P j := by
    by_contra hc
    push_neg at hc
    have : ∑ j, P j ≤ 0 := sum_nonpos fun j _ => hc j
    linarith
  obtain ⟨j, hj⟩ := hne
  exact lt_of_lt_of_le (mul_pos hj (Real.exp_pos _))
    (single_le_sum (f := fun j => P j * Real.exp (t * y j))
      (fun i _ => mul_nonneg (hP i) (Real.exp_pos _).le) (mem_univ j))

private lemma holder_exponential_moments {ι : Type} [Fintype ι] (P y : ι → ℝ) (hP : ∀ j, 0 ≤ P j)
    (s t a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    ∑ j, P j * Real.exp ((a * s + b * t) * y j) ≤
      (∑ j, P j * Real.exp (s * y j)) ^ a * (∑ j, P j * Real.exp (t * y j)) ^ b := by
  have hzero : ∀ u : ℝ, ∑ j, P j * Real.exp (u * y j) = 0 → ∀ j, P j = 0 := by
    intro u hu j
    have := (sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (hP i) (Real.exp_pos (u * y i)).le)).1 hu j (mem_univ j)
    exact (mul_eq_zero.1 this).resolve_right (Real.exp_pos _).ne'
  have hL0 : (∀ j, P j = 0) → ∑ j, P j * Real.exp ((a * s + b * t) * y j) = 0 := by
    intro h0; simp [h0]
  have hS0 : 0 ≤ ∑ j, P j * Real.exp (s * y j) :=
    sum_nonneg fun j _ => mul_nonneg (hP j) (Real.exp_pos _).le
  have hT0 : 0 ≤ ∑ j, P j * Real.exp (t * y j) :=
    sum_nonneg fun j _ => mul_nonneg (hP j) (Real.exp_pos _).le
  rcases hS0.eq_or_lt with hS | hS
  · rw [hL0 (hzero s hS.symm), ← hS, Real.zero_rpow ha.ne', zero_mul]
  rcases hT0.eq_or_lt with hT | hT
  · rw [hL0 (hzero t hT.symm), ← hT, Real.zero_rpow hb.ne', mul_zero]
  set S := ∑ j, P j * Real.exp (s * y j) with hSdef
  set T := ∑ j, P j * Real.exp (t * y j) with hTdef
  have key : ∀ j, Real.exp ((a * s + b * t) * y j) =
      Real.exp (s * y j) ^ a * Real.exp (t * y j) ^ b := by
    intro j
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  have hSa : 0 < S ^ a := Real.rpow_pos_of_pos hS a
  have hTb : 0 < T ^ b := Real.rpow_pos_of_pos hT b
  have pt : ∀ j, P j * Real.exp ((a * s + b * t) * y j) / (S ^ a * T ^ b) ≤
      a * (P j * Real.exp (s * y j) / S) + b * (P j * Real.exp (t * y j) / T) := by
    intro j
    have g := Real.geom_mean_le_arith_mean2_weighted ha.le hb.le
      (div_nonneg (Real.exp_pos (s * y j)).le hS.le)
      (div_nonneg (Real.exp_pos (t * y j)).le hT.le) hab
    rw [Real.div_rpow (Real.exp_pos _).le hS.le, Real.div_rpow (Real.exp_pos _).le hT.le] at g
    rw [key j]
    calc P j * (Real.exp (s * y j) ^ a * Real.exp (t * y j) ^ b) / (S ^ a * T ^ b)
        = P j * (Real.exp (s * y j) ^ a / S ^ a * (Real.exp (t * y j) ^ b / T ^ b)) := by
          field_simp
      _ ≤ P j * (a * (Real.exp (s * y j) / S) + b * (Real.exp (t * y j) / T)) :=
          mul_le_mul_of_nonneg_left g (hP j)
      _ = a * (P j * Real.exp (s * y j) / S) + b * (P j * Real.exp (t * y j) / T) := by ring
  have hsum := sum_le_sum fun j (_ : j ∈ univ) => pt j
  have e1 : ∑ j, (a * (P j * Real.exp (s * y j) / S) + b * (P j * Real.exp (t * y j) / T)) = 1 := by
    simp only [sum_add_distrib, ← mul_sum, ← sum_div]
    rw [← hSdef, ← hTdef, div_self hS.ne', div_self hT.ne', mul_one, mul_one, hab]
  rw [e1, ← sum_div, div_le_one (mul_pos hSa hTb)] at hsum
  exact hsum

theorem log_moment_convexity : LogMomentConvexity := by
  intro ι _ P y hP h1
  have hpos := fun t => exponential_moment_pos P y hP h1 t
  have hconv : ConvexOn ℝ Set.univ (fun t : ℝ => Real.log (∑ j, P j * Real.exp (t * y j))) := by
    refine ⟨convex_univ, ?_⟩
    intro s _ t _ a b ha hb hab
    simp only [smul_eq_mul]
    rcases ha.eq_or_lt with ha0 | ha0
    · subst ha0
      have hb1 : b = 1 := by linarith
      subst hb1
      simp
    rcases hb.eq_or_lt with hb0 | hb0
    · subst hb0
      have ha1 : a = 1 := by linarith
      subst ha1
      simp
    have hh := holder_exponential_moments P y hP s t a b ha0 hb0 hab
    calc Real.log (∑ j, P j * Real.exp ((a * s + b * t) * y j))
        ≤ Real.log ((∑ j, P j * Real.exp (s * y j)) ^ a * (∑ j, P j * Real.exp (t * y j)) ^ b) :=
          Real.log_le_log (hpos _) hh
      _ = a * Real.log (∑ j, P j * Real.exp (s * y j)) +
            b * Real.log (∑ j, P j * Real.exp (t * y j)) := by
          rw [Real.log_mul (Real.rpow_pos_of_pos (hpos s) a).ne' (Real.rpow_pos_of_pos (hpos t) b).ne',
            Real.log_rpow (hpos s), Real.log_rpow (hpos t)]
  refine ⟨hconv, ?_⟩
  intro t₀ t ht₀ ht
  have htpos : 0 < t := lt_of_lt_of_le ht₀ ht
  have ht0ne : t₀ ≠ 0 := ht₀.ne'
  have htne : t ≠ 0 := htpos.ne'
  have hf0 : Real.log (∑ j, P j * Real.exp (0 * y j)) = 0 := by simp [h1]
  have hc := hconv.2 (Set.mem_univ t) (Set.mem_univ 0) (div_nonneg ht₀.le htpos.le)
    (sub_nonneg.2 ((div_le_one htpos).2 ht)) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, hf0] at hc
  have e : t₀ / t * t = t₀ := by field_simp
  rw [e] at hc
  calc t / t₀ * Real.log (∑ j, P j * Real.exp (t₀ * y j))
      ≤ t / t₀ * (t₀ / t * Real.log (∑ j, P j * Real.exp (t * y j))) :=
        mul_le_mul_of_nonneg_left hc (div_nonneg htpos.le ht₀.le)
    _ = Real.log (∑ j, P j * Real.exp (t * y j)) := by
        rw [← mul_assoc, div_mul_div_comm, mul_comm t t₀, div_self (mul_ne_zero ht0ne htne), one_mul]

private lemma half_le_gamma_succ (x : ℝ) (hx : 1 ≤ x) (h : 1 / 2 ≤ Real.Gamma x) :
    1 / 2 ≤ Real.Gamma (x + 1) := by
  rw [Real.Gamma_add_one (by linarith)]
  nlinarith

private lemma half_le_gamma_half_nat (n : ℕ) (hn : 2 ≤ n) : 1 / 2 ≤ Real.Gamma ((n : ℝ) / 2) := by
  revert hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
    · norm_num [Real.Gamma_one]
    · have e : ((3 : ℕ) : ℝ) / 2 = 1 / 2 + 1 := by norm_num
      rw [e, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
      have : (1 : ℝ) ≤ Real.sqrt Real.pi := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
      linarith
    · have e : (n : ℝ) / 2 = ((n - 2 : ℕ) : ℝ) / 2 + 1 := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      have hx : (2 : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ n - 2)
      rw [e]
      exact half_le_gamma_succ _ (by linarith) (ih (n - 2) (by omega) (by omega))

theorem tail_negligible : TailNegligible := by
  refine ⟨20, ?_⟩
  intro n Q hn hQ
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hL : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
  have hnL : (n : ℝ) * Real.log 2 ≤ n * Real.log n := mul_le_mul_of_nonneg_left hL hn0
  have hnl2 : (0.6931471803 : ℝ) * n ≤ n * Real.log 2 := by nlinarith
  have hQpos : 0 < Q := by nlinarith
  have h2n : (0 : ℝ) < 2 * n := by linarith
  have hlogQ : Real.log Q ≤ Q / (2 * n) - 1 + (Real.log 2 + Real.log n) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hQpos h2n)
    rw [Real.log_div hQpos.ne' h2n.ne', Real.log_mul (by norm_num) (by linarith)] at h1
    linarith
  have hm : (n : ℝ) / 2 * Real.log Q ≤
      Q / 4 - n / 2 + n / 2 * Real.log 2 + n / 2 * Real.log n := by
    have h1 := mul_le_mul_of_nonneg_left hlogQ (by linarith : (0 : ℝ) ≤ n / 2)
    have e : (n : ℝ) / 2 * (Q / (2 * n) - 1 + (Real.log 2 + Real.log n)) =
        Q / 4 - n / 2 + n / 2 * Real.log 2 + n / 2 * Real.log n := by
      have hnne : (n : ℝ) ≠ 0 := by linarith
      first | (field_simp; ring) | field_simp | ring
    linarith
  have hG := half_le_gamma_half_nat n hn
  have hQm : 0 < Q ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos hQpos _
  have h4Qm : 0 < 4 * Q ^ ((n : ℝ) / 2) := by linarith
  have h2Qm : 0 < 2 * Q ^ ((n : ℝ) / 2) := by linarith
  have hE : (3 : ℝ) ≤ -(n : ℝ) + Q / 2 - Real.log Q * ((n : ℝ) / 2) := by nlinarith
  have hexp : Real.exp (-(Q / 2)) * (4 * Q ^ ((n : ℝ) / 2)) ≤ Real.exp (-(n : ℝ)) := by
    rw [Real.rpow_def_of_pos hQpos]
    have h4 : (4 : ℝ) ≤ Real.exp (-(n : ℝ) + Q / 2 - Real.log Q * ((n : ℝ) / 2)) := by
      have := Real.add_one_le_exp (-(n : ℝ) + Q / 2 - Real.log Q * ((n : ℝ) / 2))
      linarith
    calc Real.exp (-(Q / 2)) * (4 * Real.exp (Real.log Q * ((n : ℝ) / 2)))
        ≤ Real.exp (-(Q / 2)) * (Real.exp (-(n : ℝ) + Q / 2 - Real.log Q * ((n : ℝ) / 2)) *
            Real.exp (Real.log Q * ((n : ℝ) / 2))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
      _ = Real.exp (-(n : ℝ)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
  calc Real.exp (-(Q / 2))
      = Real.exp (-(Q / 2)) * (4 * Q ^ ((n : ℝ) / 2)) / (4 * Q ^ ((n : ℝ) / 2)) := by
        rw [mul_div_assoc, div_self h4Qm.ne', mul_one]
    _ ≤ Real.exp (-(n : ℝ)) / (4 * Q ^ ((n : ℝ) / 2)) := by gcongr
    _ = Real.exp (-(n : ℝ)) * (1 / 2 / (2 * Q ^ ((n : ℝ) / 2))) := by
        rw [div_div, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num, mul_one_div]
    _ ≤ Real.exp (-(n : ℝ)) * (Real.Gamma ((n : ℝ) / 2) / (2 * Q ^ ((n : ℝ) / 2))) := by
        gcongr

private lemma prod_range_factorial_pos (n : ℕ) : 0 < ∏ i ∈ range n, (i.factorial : ℝ) :=
  prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i

theorem grassmannian_volume : GrassmannianVolume := by
  intro p q
  have hF : ∀ n, 0 < ∏ i ∈ range n, (i.factorial : ℝ) := prod_range_factorial_pos
  have hPpos : ∀ n, 0 < ∏ i ∈ range n, Real.pi ^ (i + 1) :=
    fun n => prod_pos fun i _ => pow_pos Real.pi_pos _
  have hA : ∀ n, ∏ i ∈ range n, 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ) =
      2 ^ n * (∏ i ∈ range n, Real.pi ^ (i + 1)) / ∏ i ∈ range n, (i.factorial : ℝ) := by
    intro n
    rw [prod_div_distrib, prod_mul_distrib, prod_const, card_range]
  have hP : ∏ i ∈ range (p + q), Real.pi ^ (i + 1) =
      (∏ i ∈ range p, Real.pi ^ (i + 1)) * (∏ i ∈ range q, Real.pi ^ (i + 1)) *
        Real.pi ^ (p * q) := by
    rw [prod_range_add]
    have e : ∀ j ∈ range q, Real.pi ^ (p + j + 1) = Real.pi ^ p * Real.pi ^ (j + 1) := by
      intro j _
      rw [← pow_add]
      congr 1
    rw [prod_congr rfl e, prod_mul_distrib, prod_const, card_range, ← pow_mul]
    ring
  have hFF : (∏ i ∈ range p, (i.factorial : ℝ)) * ∏ i ∈ range q, (i.factorial : ℝ) ≤
      ∏ i ∈ range (p + q), (i.factorial : ℝ) := by
    rw [prod_range_add]
    apply mul_le_mul_of_nonneg_left _ (hF p).le
    apply prod_le_prod (fun i _ => by positivity) (fun i _ => ?_)
    exact_mod_cast Nat.factorial_le (by omega)
  have h1 := (hF p).ne'
  have h2 := (hF q).ne'
  have h3 := (hF (p + q)).ne'
  have h4 := (hPpos p).ne'
  have h5 := (hPpos q).ne'
  refine ⟨?_, ?_⟩
  · rw [hA, hA, hA, hP, pow_add]
    field_simp
  · rw [mul_div_assoc]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (hF _)).2 hFF)

end Formalism.HermitianLattices.GenusMassVolumes
