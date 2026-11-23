import Formalism.HermitianCurvature.StatementSz

namespace Formalism.FourierDecayAlt.P.Sz4

open Finset Formalism.FourierDecayAlt.Sz

lemma sum_pairs_reindex (J : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J, F i j =
      ∑ d ∈ Ioc 0 J, ∑ i ∈ Icc 1 (J - d), F i (i + d) := by
  have h1 : ∀ i ∈ Icc 1 J, ∑ j ∈ Ioc i J, F i j = ∑ d ∈ Ioc 0 (J - i), F i (i + d) := by
    intro i hi
    rw [mem_Icc] at hi
    refine Finset.sum_nbij' (fun j => j - i) (fun d => i + d) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [mem_Ioc] at hj ⊢; omega
    · intro d hd; simp only [mem_Ioc] at hd ⊢; omega
    · intro j hj; simp only [mem_Ioc] at hj; omega
    · intro d hd; omega
    · intro j hj; simp only [mem_Ioc] at hj; congr 1; omega
  rw [Finset.sum_congr rfl h1]
  refine Finset.sum_comm' ?_
  intro i d
  simp only [mem_Icc, mem_Ioc]
  omega

lemma tele (g : ℕ → ℝ) (n : ℕ) : ∑ i ∈ Icc 1 n, (g (i + 1) - g i) = g (n + 1) - g 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring

lemma shift_bound1 (de : ℕ → ℝ) (h01 : ∀ i, de i = 0 ∨ de i = 1) (n d : ℕ) :
    |∑ i ∈ Icc 1 n, (de (i + d) - de i)| ≤ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h : ∑ i ∈ Icc 1 n, (de (i + (d + 1)) - de i) =
        ∑ i ∈ Icc 1 n, (de (i + d) - de i) + (de (n + 1 + d) - de (1 + d)) := by
      have := tele (fun i => de (i + d)) n
      rw [← this, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : i + (d + 1) = i + 1 + d := by ring
      rw [this]; ring
    rw [h]
    have h2 : |de (n + 1 + d) - de (1 + d)| ≤ 1 := by
      rcases h01 (n + 1 + d) with a | a <;> rcases h01 (1 + d) with b | b <;> rw [a, b] <;> norm_num
    calc _ ≤ |∑ i ∈ Icc 1 n, (de (i + d) - de i)| + |de (n + 1 + d) - de (1 + d)| := abs_add_le _ _
      _ ≤ (d : ℝ) + 1 := by linarith
      _ = ((d + 1 : ℕ) : ℝ) := by push_cast; ring

lemma shift_bound2 (de : ℕ → ℝ) (h01 : ∀ i, de i = 0 ∨ de i = 1) (n d : ℕ) :
    |∑ i ∈ Icc 1 n, (de (i + d) - de i)| ≤ n := by
  calc _ ≤ ∑ i ∈ Icc 1 n, |de (i + d) - de i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Icc 1 n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rcases h01 (i + d) with a | a <;> rcases h01 i with b | b <;> rw [a, b] <;> norm_num
    _ = n := by simp

lemma harm_log (h n : ℕ) (hh : 1 ≤ h) (hn : h ≤ n) :
    ∑ d ∈ Ioc h n, (1 : ℝ) / d ≤ Real.log n - Real.log h := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ioc_succ_top hn]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have := Real.one_sub_inv_le_log_of_pos (x := ((n : ℝ) + 1) / n) (by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at this
    have e : 1 - (((n : ℝ) + 1) / n)⁻¹ = 1 / ((n : ℝ) + 1) := by field_simp; ring
    push_cast
    linarith

lemma sum_inv_sq_le_sub (n : ℕ) (hn : 2 ≤ n) : ∑ d ∈ Ioc 0 n, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 7 / 4 - 1 / n := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega)]
    norm_num
  | succ n hn ih =>
    rw [Finset.sum_Ioc_succ_top (by omega)]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / n - 1 / ((n : ℝ) + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast
    linarith

lemma sq_sum (n : ℕ) : ∑ d ∈ Ioc 0 n, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 7 / 4 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · norm_num
    · rw [Finset.sum_Ioc_succ_top (by omega)]; norm_num
  · have := sum_inv_sq_le_sub n h
    have h2 : (0 : ℝ) ≤ 1 / n := by positivity
    linarith

lemma one_add_ge (t : ℝ) (ht : |t| ≤ 1 / 4) : Real.exp (t - 2 / 3 * t ^ 2) ≤ 1 + t := by
  have h1 : |(-t)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le h1 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg] at h
  have hpos : 0 < 1 + t := by have := abs_le.mp ht; linarith
  rw [← Real.le_log_iff_exp_le hpos]
  have h3 := (abs_le.mp h).1
  have hs0 : 0 ≤ |t| := abs_nonneg t
  have hs2 : |t| ^ 2 = t ^ 2 := sq_abs t
  have h4 : |t| ^ 4 / (1 - |t|) ≤ t ^ 2 / 12 := by
    rw [div_le_iff₀ (by linarith)]
    rw [← hs2]
    nlinarith [mul_nonneg hs0 hs0, pow_nonneg hs0 2, pow_nonneg hs0 3]
  have h5 : -(t ^ 2 / 4) ≤ t ^ 3 := by
    have : |t ^ 3| = |t| ^ 3 := abs_pow t 3
    have h6 := neg_abs_le (t ^ 3)
    rw [this] at h6
    rw [← hs2]
    nlinarith [mul_nonneg hs0 hs0]
  have e : 1 - -t = 1 + t := by ring
  rw [e] at h3
  norm_num at h3
  nlinarith

lemma lin_bound (J : ℕ) (hJ : 1 ≤ J) (de : ℕ → ℝ) (h01 : ∀ i, de i = 0 ∨ de i = 1) :
    |∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J, (de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))| ≤
      (1 + J * Real.log 2) / 4 := by
  rw [sum_pairs_reindex]
  set B : ℕ → ℝ := fun d => ∑ i ∈ Icc 1 (J - d), (de (i + d) - de i) with hB
  have h1 : ∀ d ∈ Ioc 0 J, ∑ i ∈ Icc 1 (J - d),
      (de (i + d) - de i) / (4 * (((i + d : ℕ) : ℝ) - (i : ℝ))) = B d / (4 * d) := by
    intro d _
    rw [hB]; simp only
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1; push_cast; ring
  rw [Finset.sum_congr rfl h1]
  set h : ℕ := (J + 1) / 2 with hh
  have hh1 : 1 ≤ h := by omega
  have hhJ : h ≤ J := by omega
  have hJ2 : J ≤ 2 * h := by omega
  have h2J : 2 * h ≤ J + 1 := by omega
  have hJ2R : (J : ℝ) ≤ 2 * h := by exact_mod_cast hJ2
  have h2JR : 2 * (h : ℝ) ≤ J + 1 := by exact_mod_cast h2J
  have hhpos : (0 : ℝ) < h := by exact_mod_cast hh1
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  calc |∑ d ∈ Ioc 0 J, B d / (4 * d)| ≤ ∑ d ∈ Ioc 0 J, |B d / (4 * d)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ Ioc 0 h, |B d / (4 * d)| + ∑ d ∈ Ioc h J, |B d / (4 * d)| :=
        (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hhJ).symm
    _ ≤ ∑ _d ∈ Ioc 0 h, (1 / 4 : ℝ) + ∑ d ∈ Ioc h J, ((J : ℝ) / 4 * (1 / d) - 1 / 4) := by
        refine add_le_add (Finset.sum_le_sum fun d hd => ?_) (Finset.sum_le_sum fun d hd => ?_)
        · rw [mem_Ioc] at hd
          have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
          rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * d), div_le_iff₀ (by positivity)]
          have := shift_bound1 de h01 (J - d) d
          linarith
        · rw [mem_Ioc] at hd
          have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
          rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * d), div_le_iff₀ (by positivity)]
          have := shift_bound2 de h01 (J - d) d
          rw [Nat.cast_sub hd.2] at this
          have e : ((J : ℝ) / 4 * (1 / d) - 1 / 4) * (4 * d) = J - d := by field_simp
          rw [e]; exact this
    _ = (h : ℝ) / 4 + ((J : ℝ) / 4 * ∑ d ∈ Ioc h J, (1 : ℝ) / d - ((J : ℝ) - h) / 4) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.cast_sub hhJ]
        simp; ring
    _ ≤ (h : ℝ) / 4 + ((J : ℝ) / 4 * Real.log 2 - ((J : ℝ) - h) / 4) := by
        have h3 := harm_log h J hh1 hhJ
        have h4 : Real.log J - Real.log h ≤ Real.log 2 := by
          rw [← Real.log_div (ne_of_gt hJpos) (ne_of_gt hhpos)]
          apply Real.log_le_log (by positivity)
          rw [div_le_iff₀ hhpos]; exact hJ2R
        have h5 : (J : ℝ) / 4 * ∑ d ∈ Ioc h J, (1 : ℝ) / d ≤ (J : ℝ) / 4 * Real.log 2 :=
          mul_le_mul_of_nonneg_left (h3.trans h4) (by positivity)
        linarith
    _ ≤ (1 + J * Real.log 2) / 4 := by linarith

lemma quad_bound (J : ℕ) (de : ℕ → ℝ) (h01 : ∀ i, de i = 0 ∨ de i = 1) :
    ∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J, ((de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))) ^ 2 ≤
      7 / 64 * (J : ℝ) := by
  rw [sum_pairs_reindex]
  calc _ ≤ ∑ d ∈ Ioc 0 J, (J : ℝ) / 16 * (1 / (d : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun d hd => ?_
        rw [mem_Ioc] at hd
        have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
        calc _ ≤ ∑ _i ∈ Icc 1 (J - d), (1 : ℝ) / 16 * (1 / (d : ℝ) ^ 2) := by
              refine Finset.sum_le_sum fun i _ => ?_
              have e : ((i + d : ℕ) : ℝ) - (i : ℝ) = d := by push_cast; ring
              rw [e, div_pow, mul_pow]
              have h2 : (de (i + d) - de i) ^ 2 ≤ 1 := by
                rcases h01 (i + d) with a | a <;> rcases h01 i with b | b <;> rw [a, b] <;> norm_num
              rw [div_le_iff₀ (by positivity)]
              have e2 : (1 : ℝ) / 16 * (1 / (d : ℝ) ^ 2) * (4 ^ 2 * (d : ℝ) ^ 2) = 1 := by
                field_simp; norm_num
              rw [e2]; exact h2
          _ = ((J - d : ℕ) : ℝ) * ((1 : ℝ) / 16 * (1 / (d : ℝ) ^ 2)) := by simp
          _ ≤ (J : ℝ) * ((1 : ℝ) / 16 * (1 / (d : ℝ) ^ 2)) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact_mod_cast Nat.sub_le J d
          _ = _ := by ring
    _ = (J : ℝ) / 16 * ∑ d ∈ Ioc 0 J, (1 : ℝ) / (d : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (J : ℝ) / 16 * (7 / 4) := mul_le_mul_of_nonneg_left (sq_sum J) (by positivity)
    _ = _ := by ring

lemma pair_small (de : ℕ → ℝ) (h01 : ∀ i, de i = 0 ∨ de i = 1) (i j : ℕ) (hij : i < j) :
    |(de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))| ≤ 1 / 4 := by
  have h1 : (1 : ℝ) ≤ (j : ℝ) - i := by
    have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    linarith
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 4 * ((j : ℝ) - i)), div_le_iff₀ (by linarith)]
  have h2 : |de j - de i| ≤ 1 := by
    rcases h01 j with a | a <;> rcases h01 i with b | b <;> rw [a, b] <;> norm_num
  linarith

lemma rde_bound (J : ℕ) (hJ : 1 ≤ J) (de : ℕ → ℝ) (h01 : ∀ i, de i = 0 ∨ de i = 1) :
    Real.exp (-(((J : ℝ) + 1) / 4)) ≤ Rde J de ∧ Rde J de ≤ Real.exp (((J : ℝ) + 1) / 4) := by
  have hlin := abs_le.mp (lin_bound J hJ de h01)
  have hquad := quad_bound J de h01
  have hlog2 := Real.log_two_lt_d9
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  constructor
  · calc Real.exp (-(((J : ℝ) + 1) / 4))
        ≤ Real.exp (∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J,
            ((de j - de i) / (4 * ((j : ℝ) - (i : ℝ))) -
              2 / 3 * ((de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))) ^ 2)) := by
          apply Real.exp_le_exp.mpr
          simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
          nlinarith [hlin.1]
      _ = ∏ i ∈ Icc 1 J, ∏ j ∈ Ioc i J, Real.exp
            ((de j - de i) / (4 * ((j : ℝ) - (i : ℝ))) -
              2 / 3 * ((de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))) ^ 2) := by
          rw [Real.exp_sum]
          exact Finset.prod_congr rfl fun i _ => Real.exp_sum _ _
      _ ≤ Rde J de := by
          unfold Rde
          refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => (Real.exp_pos _).le)
            fun i _ => ?_
          refine Finset.prod_le_prod (fun j _ => (Real.exp_pos _).le) fun j hj => ?_
          exact one_add_ge _ (pair_small de h01 i j (mem_Ioc.mp hj).1)
  · calc Rde J de ≤ ∏ i ∈ Icc 1 J, ∏ j ∈ Ioc i J, Real.exp
            ((de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))) := by
          unfold Rde
          have hnn : ∀ i j : ℕ, j ∈ Ioc i J → 0 ≤ 1 + (de j - de i) / (4 * ((j : ℝ) - (i : ℝ))) := by
            intro i j hj
            have := abs_le.mp (pair_small de h01 i j (mem_Ioc.mp hj).1)
            linarith [this.1]
          refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j hj => hnn i j hj)
            fun i _ => ?_
          refine Finset.prod_le_prod (fun j hj => hnn i j hj) fun j hj => ?_
          rw [add_comm]; exact Real.add_one_le_exp _
      _ = Real.exp (∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J, (de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))) := by
          rw [Real.exp_sum]
          exact (Finset.prod_congr rfl fun i _ => Real.exp_sum _ _).symm
      _ ≤ Real.exp (((J : ℝ) + 1) / 4) := by
          apply Real.exp_le_exp.mpr
          nlinarith [hlin.2]

lemma prod_shift (p : ℕ) (f : ℕ → ℝ) : ∏ i ∈ Icc 1 p, f (i + 1) = ∏ i ∈ Icc 2 (p + 1), f i := by
  refine Finset.prod_nbij' (fun i => i + 1) (fun i => i - 1) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [mem_Icc] at hi ⊢; omega
  · intro i hi; simp only [mem_Icc] at hi ⊢; omega
  · intro i hi; simp only [mem_Icc] at hi; omega
  · intro i hi; simp only [mem_Icc] at hi; omega
  · intro i _; rfl

lemma prod_shift_Ioc (i p : ℕ) (f : ℕ → ℝ) :
    ∏ j ∈ Ioc i p, f (j + 1) = ∏ j ∈ Ioc (i + 1) (p + 1), f j := by
  refine Finset.prod_nbij' (fun i => i + 1) (fun i => i - 1) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [mem_Ioc] at hj ⊢; omega
  · intro j hj; simp only [mem_Ioc] at hj ⊢; omega
  · intro j hj; simp only [mem_Ioc] at hj; omega
  · intro j hj; simp only [mem_Ioc] at hj; omega
  · intro j _; rfl

lemma vand_ratio (p : ℕ) (x y : ℕ → ℝ) (r : ℕ → ℕ → ℝ)
    (h : ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ p → x i - x j = r i j * (y i - y j)) :
    Vand p x = (∏ i ∈ Icc 1 p, ∏ j ∈ Ioc i p, r i j) * Vand p y := by
  unfold Vand
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  exact h i j (mem_Icc.mp hi).1 (mem_Ioc.mp hj).1 (mem_Ioc.mp hj).2

lemma vand_pos (p : ℕ) (x : ℕ → ℝ) (h : ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ p → x j < x i) :
    0 < Vand p x := by
  unfold Vand
  refine Finset.prod_pos fun i hi => Finset.prod_pos fun j hj => ?_
  have := h i j (mem_Icc.mp hi).1 (mem_Ioc.mp hj).1 (mem_Ioc.mp hj).2
  linarith

lemma vand_succ_top (p : ℕ) (x : ℕ → ℝ) :
    Vand (p + 1) x = Vand p x * ∏ i ∈ Icc 1 p, (x i - x (p + 1)) := by
  unfold Vand
  rw [Finset.prod_Icc_succ_top (by omega), Finset.Ioc_self, Finset.prod_empty, mul_one,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.prod_Ioc_succ_top (mem_Icc.mp hi).2]

lemma vand_succ_bot (p : ℕ) (x : ℕ → ℝ) :
    Vand (p + 1) x = (∏ j ∈ Icc 2 (p + 1), (x 1 - x j)) * Vand p (fun i => x (i + 1)) := by
  unfold Vand
  have h1 : Icc 1 (p + 1) = insert 1 (Icc 2 (p + 1)) := by
    ext a; simp only [mem_Icc, mem_insert]; omega
  have h2 : Ioc 1 (p + 1) = Icc 2 (p + 1) := by
    ext a; simp only [mem_Icc, mem_Ioc]; omega
  rw [h1, Finset.prod_insert (by simp), h2]
  congr 1
  rw [← prod_shift p (fun i => ∏ j ∈ Ioc i (p + 1), (x i - x j))]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (prod_shift_Ioc i p (fun j => x (i + 1) - x j)).symm

lemma prod_refl (p : ℕ) : ∏ i ∈ Icc 1 p, (((p + 1 : ℕ) : ℝ) - (i : ℝ)) = (p.factorial : ℝ) := by
  have hf : ∀ n : ℕ, ∏ i ∈ Icc 1 n, (i : ℝ) = (n.factorial : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]; push_cast; ring
  rw [← hf p]
  refine Finset.prod_nbij' (fun i => p + 1 - i) (fun i => p + 1 - i) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [mem_Icc] at hi ⊢; omega
  · intro i hi; simp only [mem_Icc] at hi ⊢; omega
  · intro i hi; simp only [mem_Icc] at hi; omega
  · intro i hi; simp only [mem_Icc] at hi; omega
  · intro i hi; simp only [mem_Icc] at hi; rw [Nat.cast_sub (by omega)]

lemma v_sub (c : Cfg) (i j : ℕ) : c.v i - c.v j = 4 * c.Del * ((j : ℝ) - (i : ℝ)) := by
  unfold Cfg.v; ring

lemma v_anti (c : Cfg) (hc : c.Ok) (i j : ℕ) (hij : i < j) : c.v j < c.v i := by
  have h := v_sub c i j
  have h1 : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
  have h2 := hc.hDel
  nlinarith

lemma u_succ (c : Cfg) (de : ℕ → ℝ) (hw : IsWord c.k de) (i : ℕ) (hi : 1 ≤ i)
    (_hik : i + 1 ≤ c.k) (h : i + 2 ≤ c.k ∨ c.top = false) :
    c.u de (i + 1) = c.v i - 1 / 2 - de i * c.Del := by
  have h1 : i + 1 ≠ 1 := by omega
  by_cases hlast : i + 1 = c.k
  · have ht : c.top = false := by
      rcases h with h | h
      · omega
      · exact h
    have hi' : i = c.k - 1 := by omega
    have hde : de i = 0 := by rw [hi']; exact hw.2
    have hiR : (i : ℝ) + 1 = c.k := by exact_mod_cast hlast
    unfold Cfg.u; rw [if_neg h1, if_pos hlast, hde]
    unfold Cfg.ulast Cfg.v; rw [← hiR]; simp [ht]
  · unfold Cfg.u; rw [if_neg h1, if_neg hlast]; simp

lemma position_ratio (c : Cfg) (de : ℕ → ℝ) (hw : IsWord c.k de) (i j : ℕ) (hi : 1 ≤ i)
    (hij : i < j) (hj : j + 1 ≤ c.k) (h : j + 2 ≤ c.k ∨ c.top = false) :
    c.u de (i + 1) - c.u de (j + 1) =
      (1 + (de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))) * (c.v i - c.v j) := by
  rw [u_succ c de hw i hi (by omega) (Or.inl (by omega)), u_succ c de hw j (by omega) hj h, v_sub]
  have hpos : (0 : ℝ) < (j : ℝ) - i := by
    have : (i : ℝ) < j := by exact_mod_cast hij
    linarith
  have h3 := v_sub c i j
  field_simp
  linarith

lemma vand_words_ratio (c : Cfg) (de : ℕ → ℝ) (hw : IsWord c.k de) (p : ℕ) (hp : p + 1 ≤ c.k)
    (h : p + 2 ≤ c.k ∨ c.top = false) :
    Vand p (fun i => c.u de (i + 1)) = Rde p de * Vand p c.v := by
  unfold Rde
  refine vand_ratio p (fun i => c.u de (i + 1)) c.v
    (fun i j => 1 + (de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))) ?_
  intro i j hi hij hj
  refine position_ratio c de hw i j hi hij (by omega) ?_
  rcases h with h | h
  · left; omega
  · right; exact h

end Formalism.FourierDecayAlt.P.Sz4

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.Sz Formalism.FourierDecayAlt.P.Sz4

theorem vandermondeNonTop : Formalism.FourierDecayAlt.Sz.VandNonTop := by
  intro c de hc hw ht
  have hk := hc.hk
  have hcast : ((c.k - 1 : ℕ) : ℝ) + 1 = c.k := by
    rw [Nat.cast_sub (by omega)]; simp
  have hb := rde_bound (c.k - 1) (by omega) de hw.1
  rw [hcast] at hb
  exact ⟨vand_pos _ _ fun i j _ hij _ => v_anti c hc i j hij,
    vand_words_ratio c de hw (c.k - 1) (by omega) (Or.inr ht), hb.1, hb.2⟩

theorem vandermondeTop : Formalism.FourierDecayAlt.Sz.VandTop := by
  intro c de hc hw
  have hk := hc.hk
  have hcast : ((c.k - 2 : ℕ) : ℝ) + 1 = (c.k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hb := rde_bound (c.k - 2) (by omega) de hw.1
  rw [hcast] at hb
  refine ⟨vand_pos _ _ fun i j _ hij _ => v_anti c hc i j hij,
    vand_words_ratio c de hw (c.k - 2) (by omega) (Or.inl (by omega)), hb.1, hb.2, ?_⟩
  have h := vand_succ_top (c.k - 2) c.v
  have e : c.k - 2 + 1 = c.k - 1 := by omega
  have h2 : ∏ i ∈ Icc 1 (c.k - 2), (c.v i - c.v (c.k - 2 + 1)) =
      (4 * c.Del) ^ (c.k - 2) * ((c.k - 2).factorial : ℝ) := by
    rw [← prod_refl (c.k - 2)]
    simp only [v_sub]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
    simp
  rw [h2, e] at h
  rw [h]; ring

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.Sz4

open Finset Formalism.FourierDecayAlt.Sz

lemma v_one_nonneg (c : Cfg) (hc : c.Ok) : 0 ≤ c.v 1 := by
  have hk : (4 : ℝ) ≤ c.k := by exact_mod_cast hc.hk
  have h1 := hc.hDel
  have h2 := hc.hv0
  unfold Cfg.v
  push_cast
  nlinarith

lemma edge_factor (c : Cfg) (de : ℕ → ℝ) (hc : c.Ok) (hw : IsWord c.k de) (i : ℕ) (h2 : 2 ≤ i)
    (hik : i ≤ c.k) (h : i < c.k ∨ c.top = false) :
    c.a - c.v 1 ≤ c.a - c.u de i ∧ c.a - c.u de i ≤ 2 * (c.a - c.v 1) := by
  obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by omega⟩
  have h' : l + 2 ≤ c.k ∨ c.top = false := by
    rcases h with h | h
    · left; omega
    · right; exact h
  rw [u_succ c de hw l (by omega) hik h']
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  have hlk : (l : ℝ) + 1 ≤ c.k := by exact_mod_cast hik
  have hD := hc.hDel
  have ha := hc.ha
  have hv : c.v l = c.v 1 - 4 * c.Del * ((l : ℝ) - 1) := by unfold Cfg.v; push_cast; ring
  rw [hv]
  have m1 : 0 ≤ c.Del * ((l : ℝ) - 1) := mul_nonneg (by linarith) (by linarith)
  have m2 : 0 ≤ c.Del * ((c.k : ℝ) - 1 - l) := mul_nonneg (by linarith) (by linarith)
  rcases hw.1 l with e | e <;> rw [e] <;> constructor <;> nlinarith

lemma prod_ratio_le (s : Finset ℕ) (f g : ℕ → ℝ) (ε : ℝ) (hg : ∀ i ∈ s, 0 < g i)
    (hf : ∀ i ∈ s, 0 < f i) (h : ∀ i ∈ s, f i ≤ (1 + ε) * g i) :
    ∏ i ∈ s, f i / g i ≤ Real.exp ((s.card : ℝ) * ε) := by
  calc ∏ i ∈ s, f i / g i ≤ ∏ _i ∈ s, Real.exp ε := by
        refine Finset.prod_le_prod (fun i hi => (div_pos (hf i hi) (hg i hi)).le) fun i hi => ?_
        rw [div_le_iff₀ (hg i hi)]
        refine (h i hi).trans (mul_le_mul_of_nonneg_right ?_ (hg i hi).le)
        rw [add_comm]; exact Real.add_one_le_exp ε
    _ = Real.exp ((s.card : ℝ) * ε) := by rw [Finset.prod_const, Real.exp_nat_mul]

lemma prod_ratio_ge (s : Finset ℕ) (f g : ℕ → ℝ) (B : ℝ) (hg : ∀ i ∈ s, 0 < g i)
    (hf : ∀ i ∈ s, 0 < f i) (h : ∏ i ∈ s, g i / f i ≤ Real.exp B) :
    Real.exp (-B) ≤ ∏ i ∈ s, f i / g i := by
  have e : ∏ i ∈ s, f i / g i = (∏ i ∈ s, g i / f i)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun i _ => (inv_div _ _).symm
  rw [e, Real.exp_neg]
  exact inv_anti₀ (Finset.prod_pos fun i hi => div_pos (hg i hi) (hf i hi)) h

lemma u_mid (c : Cfg) (de : ℕ → ℝ) (hw : IsWord c.k de) (i : ℕ) (hi : i ∈ Icc 2 (c.k - 1)) :
    c.u de i = c.v (i - 1) - 1 / 2 - de (i - 1) * c.Del := by
  rw [mem_Icc] at hi
  have := u_succ c de hw (i - 1) (by omega) (by omega) (Or.inl (by omega))
  rwa [Nat.sub_add_cancel (by omega)] at this

lemma u_mid_diff (c : Cfg) (de de' : ℕ → ℝ) (hc : c.Ok) (hw : IsWord c.k de)
    (hw' : IsWord c.k de') (i : ℕ) (hi : i ∈ Icc 2 (c.k - 1)) :
    |c.u de i - c.u de' i| ≤ c.Del := by
  rw [u_mid c de hw i hi, u_mid c de' hw' i hi]
  have hD := hc.hDel
  rw [abs_le]
  rcases hw.1 (i - 1) with e | e <;> rcases hw'.1 (i - 1) with e' | e' <;> rw [e, e'] <;>
    constructor <;> linarith

lemma a_sub_u_pos (c : Cfg) (de : ℕ → ℝ) (hc : c.Ok) (hw : IsWord c.k de) (i : ℕ)
    (hi : i ∈ Icc 2 (c.k - 1)) : 4 * c.k * c.Del ≤ c.a - c.u de i := by
  rw [mem_Icc] at hi
  have := (edge_factor c de hc hw i hi.1 (by omega) (Or.inl (by omega))).1
  linarith [hc.ha]

lemma kDel_pos (c : Cfg) (hc : c.Ok) : 0 < 4 * (c.k : ℝ) * c.Del := by
  have hk : (4 : ℝ) ≤ c.k := by exact_mod_cast hc.hk
  have hD := hc.hDel
  positivity

lemma card_mid (c : Cfg) (hc : c.Ok) : (((Icc 2 (c.k - 1)).card : ℕ) : ℝ) = (c.k : ℝ) - 2 := by
  have hk := hc.hk
  rw [Nat.card_Icc]
  have : c.k - 1 + 1 - 2 = c.k - 2 := by omega
  rw [this, Nat.cast_sub (by omega)]; simp

lemma edge_ratio_le (c : Cfg) (de de' : ℕ → ℝ) (hc : c.Ok) (hw : IsWord c.k de)
    (hw' : IsWord c.k de') :
    ∏ i ∈ Icc 2 (c.k - 1), ((c.a - c.u de i) / (c.a - c.u de' i)) ≤ Real.exp (1 / 3) := by
  have hkD := kDel_pos c hc
  have hk : (4 : ℝ) ≤ c.k := by exact_mod_cast hc.hk
  have hD := hc.hDel
  refine (prod_ratio_le (Icc 2 (c.k - 1)) (fun i => c.a - c.u de i) (fun i => c.a - c.u de' i)
    (1 / (4 * c.k)) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)).trans ?_
  · have := a_sub_u_pos c de' hc hw' i hi; linarith
  · have := a_sub_u_pos c de hc hw i hi; linarith
  · have h1 := a_sub_u_pos c de' hc hw' i hi
    have h2 := (abs_le.mp (u_mid_diff c de de' hc hw hw' i hi)).1
    have h3 : c.Del ≤ 1 / (4 * c.k) * (c.a - c.u de' i) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
      linarith
    linarith
  · apply Real.exp_le_exp.mpr
    rw [card_mid c hc, mul_one_div, div_le_iff₀ (by positivity)]
    linarith

lemma bp_pos (c : Cfg) (hc : c.Ok) (ht : c.top = true) : 0 < c.bp := by
  have := (hc.htop ht).1
  linarith [hc.hb1]

lemma u_mid_nonneg (c : Cfg) (de : ℕ → ℝ) (hc : c.Ok) (hw : IsWord c.k de) (i : ℕ)
    (hi : i ∈ Icc 2 (c.k - 1)) : 0 ≤ c.u de i := by
  rw [u_mid c de hw i hi]
  rw [mem_Icc] at hi
  have hD := hc.hDel
  have hv0 := hc.hv0
  have hiR : ((i - 1 : ℕ) : ℝ) + 2 ≤ c.k := by exact_mod_cast (by omega : i - 1 + 2 ≤ c.k)
  have m : 0 ≤ c.Del * ((c.k : ℝ) - 2 - ((i - 1 : ℕ) : ℝ)) := mul_nonneg (by linarith) (by linarith)
  unfold Cfg.v
  rcases hw.1 (i - 1) with e | e <;> rw [e] <;> nlinarith

lemma top_ratio_le (c : Cfg) (de de' : ℕ → ℝ) (hc : c.Ok) (ht : c.top = true)
    (hw : IsWord c.k de) (hw' : IsWord c.k de') :
    ∏ i ∈ Icc 2 (c.k - 1), ((c.u de i + c.bp) / (c.u de' i + c.bp)) ≤ Real.exp (c.vthp / 3) := by
  have hk : (4 : ℝ) ≤ c.k := by exact_mod_cast hc.hk
  have hD := hc.hDel
  have hb := bp_pos c hc ht
  refine (prod_ratio_le (Icc 2 (c.k - 1)) (fun i => c.u de i + c.bp) (fun i => c.u de' i + c.bp)
    (c.Del / c.bp) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)).trans ?_
  · have := u_mid_nonneg c de' hc hw' i hi; linarith
  · have := u_mid_nonneg c de hc hw i hi; linarith
  · have h1 := u_mid_nonneg c de' hc hw' i hi
    have h2 := (abs_le.mp (u_mid_diff c de de' hc hw hw' i hi)).2
    have h3 : c.Del ≤ c.Del / c.bp * (c.u de' i + c.bp) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hb]
      nlinarith
    linarith
  · apply Real.exp_le_exp.mpr
    rw [card_mid c hc]
    have e : c.vthp = 4 * c.k * c.Del / c.bp := by simp [Cfg.vthp, ht]
    rw [e, div_div, mul_div_assoc', div_le_div_iff₀ hb (by positivity)]
    nlinarith [mul_pos hb (by linarith : (0 : ℝ) < c.Del), mul_pos (mul_pos hb (by linarith : (0 : ℝ) < c.Del)) (by linarith : (0 : ℝ) < c.k)]

end Formalism.FourierDecayAlt.P.Sz4

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.Sz Formalism.FourierDecayAlt.P.Sz4

theorem edgeFactors : Formalism.FourierDecayAlt.Sz.EdgeFactors := by
  intro c de hc hw
  refine ⟨fun i h2 hik h => edge_factor c de hc hw i h2 hik h, fun ht => ?_⟩
  have hk := hc.hk
  have hcard : (Icc 2 c.k).card = c.k - 1 := by rw [Nat.card_Icc]; omega
  have hpos : 0 ≤ c.a - c.v 1 := by
    have := kDel_pos c hc
    linarith [hc.ha]
  constructor
  · calc (c.a - c.v 1) ^ (c.k - 1) = ∏ _i ∈ Icc 2 c.k, (c.a - c.v 1) := by
          rw [Finset.prod_const, hcard]
      _ ≤ _ := by
          refine Finset.prod_le_prod (fun _ _ => hpos) fun i hi => ?_
          rw [mem_Icc] at hi
          exact (edge_factor c de hc hw i hi.1 hi.2 (Or.inr ht)).1
  · calc _ ≤ ∏ _i ∈ Icc 2 c.k, (2 * (c.a - c.v 1)) := by
          refine Finset.prod_le_prod (fun i hi => ?_) fun i hi => ?_
          · rw [mem_Icc] at hi
            exact hpos.trans (edge_factor c de hc hw i hi.1 hi.2 (Or.inr ht)).1
          · rw [mem_Icc] at hi
            exact (edge_factor c de hc hw i hi.1 hi.2 (Or.inr ht)).2
      _ = _ := by rw [Finset.prod_const, hcard]

theorem edgeRatios : Formalism.FourierDecayAlt.Sz.EdgeRatios := by
  intro c de de' hc _ hw hw'
  have hkD := kDel_pos c hc
  refine ⟨⟨?_, edge_ratio_le c de de' hc hw hw'⟩, fun ht => ⟨?_, top_ratio_le c de de' hc ht hw hw'⟩⟩
  · refine prod_ratio_ge _ (fun i => c.a - c.u de i) (fun i => c.a - c.u de' i) _
      (fun i hi => ?_) (fun i hi => ?_) (edge_ratio_le c de' de hc hw' hw)
    · have := a_sub_u_pos c de' hc hw' i hi; linarith
    · have := a_sub_u_pos c de hc hw i hi; linarith
  · have hb := bp_pos c hc ht
    refine prod_ratio_ge _ (fun i => c.u de i + c.bp) (fun i => c.u de' i + c.bp) _
      (fun i hi => ?_) (fun i hi => ?_) (top_ratio_le c de' de hc ht hw' hw)
    · have := u_mid_nonneg c de' hc hw' i hi; linarith
    · have := u_mid_nonneg c de hc hw i hi; linarith

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.Sz4

open Finset Formalism.FourierDecayAlt.Sz

lemma u_last (c : Cfg) (de : ℕ → ℝ) (hc : c.Ok) : c.u de c.k = c.ulast := by
  have : c.k ≠ 1 := by have := hc.hk; omega
  simp [Cfg.u, this]

lemma a_sub_ulast_pos (c : Cfg) (hc : c.Ok) : 0 < c.a - c.ulast := by
  have h1 := kDel_pos c hc
  have h2 := v_one_nonneg c hc
  have h3 := hc.ha
  have hk : (4 : ℝ) ≤ c.k := by exact_mod_cast hc.hk
  have hD := hc.hDel
  unfold Cfg.ulast
  by_cases ht : c.top = true
  · have := bp_pos c hc ht
    simp only [ht, if_true]; linarith
  · have hv : c.v 1 = c.vlast + 4 * c.Del * ((c.k : ℝ) - 2) := by unfold Cfg.v; push_cast; ring
    have m : 0 ≤ c.Del * ((c.k : ℝ) - 2) := mul_nonneg (by linarith) (by linarith)
    simp only [ht]; simp only [Bool.false_eq_true, if_false]; linarith

lemma vand_u_decomp (c : Cfg) (de : ℕ → ℝ) (hc : c.Ok) :
    Vand c.k (c.u de) = (∏ j ∈ Icc 2 (c.k - 1), (c.a - c.u de j)) * (c.a - c.ulast) *
      Vand (c.k - 1) (fun i => c.u de (i + 1)) := by
  have hk := hc.hk
  have h := vand_succ_bot (c.k - 1) (c.u de)
  have h2 := Finset.prod_Icc_succ_top (a := 2) (b := c.k - 1) (by omega)
    (fun j => c.u de 1 - c.u de j)
  rw [h2] at h
  rw [Nat.sub_add_cancel (by omega)] at h
  have h1 : c.u de 1 = c.a := by simp [Cfg.u]
  rw [h, h1, u_last c de hc]

lemma vand_top_decomp (c : Cfg) (de : ℕ → ℝ) (hc : c.Ok) (ht : c.top = true) :
    Vand (c.k - 1) (fun i => c.u de (i + 1)) =
      Vand (c.k - 2) (fun i => c.u de (i + 1)) * ∏ i ∈ Icc 2 (c.k - 1), (c.u de i + c.bp) := by
  have hk := hc.hk
  have h := vand_succ_top (c.k - 2) (fun i => c.u de (i + 1))
  have h2 := prod_shift (c.k - 2) (fun i => c.u de i - c.u de (c.k - 2 + 1 + 1))
  have e : c.k - 2 + 1 = c.k - 1 := by omega
  have e2 : c.k - 1 + 1 = c.k := by omega
  rw [h2] at h
  rw [e, e2, u_last c de hc] at h
  rw [h]
  have e3 : c.ulast = -c.bp := by simp [Cfg.ulast, ht]
  simp only [e3, sub_neg_eq_add]

lemma combine (E E' C R R' W α β γ M : ℝ) (hE : 0 < E) (hE' : 0 < E') (hC : 0 < C) (hW : 0 < W)
    (hβ : 0 < β) (hM : 0 < M) (h1 : E' ≤ α * E) (h2 : R' ≤ β) (h3 : γ ≤ R)
    (h4 : α * β ≤ M * γ) : E' * C * (R' * W) ≤ M * (E * C * (R * W)) := by
  have a1 : E' * R' ≤ E' * β := mul_le_mul_of_nonneg_left h2 hE'.le
  have a2 : E' * β ≤ α * E * β := mul_le_mul_of_nonneg_right h1 hβ.le
  have a3 : α * β * E ≤ M * γ * E := mul_le_mul_of_nonneg_right h4 hE.le
  have a4 : M * E * γ ≤ M * E * R := mul_le_mul_of_nonneg_left h3 (mul_pos hM hE).le
  have a5 : E' * R' ≤ M * E * R := by nlinarith
  have a6 : E' * R' * (C * W) ≤ M * E * R * (C * W) :=
    mul_le_mul_of_nonneg_right a5 (mul_pos hC hW).le
  nlinarith

lemma prod_le_of_ratio (s : Finset ℕ) (f g : ℕ → ℝ) (A : ℝ) (hg : ∀ i ∈ s, 0 < g i)
    (h : ∏ i ∈ s, f i / g i ≤ A) : ∏ i ∈ s, f i ≤ A * ∏ i ∈ s, g i := by
  rw [Finset.prod_div_distrib, div_le_iff₀ (Finset.prod_pos hg)] at h
  exact h

lemma vthp_small (c : Cfg) (hc : c.Ok) (hv : c.vth ≤ 1 / 10) (ht : c.top = true) :
    c.vthp ≤ 1 / 10 := by
  have hb := bp_pos c hc ht
  have hb1 := hc.hb1
  have hbb := (hc.htop ht).1
  have hm : (2 : ℝ) ≤ c.m := by exact_mod_cast hc.hm
  have hkD := kDel_pos c hc
  have e : c.vthp = 4 * c.k * c.Del / c.bp := by simp [Cfg.vthp, ht]
  unfold Cfg.vth at hv
  rw [div_le_iff₀ (by linarith)] at hv
  rw [e, div_le_iff₀ hb]
  have : 2 * (4 * (c.k : ℝ) * c.Del) ≤ 4 * c.m * c.k * c.Del := by nlinarith
  linarith

lemma vand_le (c : Cfg) (de de' : ℕ → ℝ) (hc : c.Ok) (hv : c.vth ≤ 1 / 10) (hw : IsWord c.k de)
    (hw' : IsWord c.k de') :
    0 < Vand c.k (c.u de) ∧
      Vand c.k (c.u de') ≤ Real.exp ((c.k : ℝ) / 2 + 1) * Vand c.k (c.u de) := by
  have hkD := kDel_pos c hc
  have hC := a_sub_ulast_pos c hc
  have hEpos : ∀ d : ℕ → ℝ, IsWord c.k d → ∀ i ∈ Icc 2 (c.k - 1), 0 < c.a - c.u d i := by
    intro d hd i hi
    have := a_sub_u_pos c d hc hd i hi; linarith
  have hE := Finset.prod_pos (hEpos de hw)
  have hE' := Finset.prod_pos (hEpos de' hw')
  have hEE := prod_le_of_ratio _ _ _ _ (hEpos de hw) (edge_ratio_le c de' de hc hw' hw)
  rw [vand_u_decomp c de hc, vand_u_decomp c de' hc]
  by_cases ht : c.top = true
  · obtain ⟨hW, hR, hR1, _, _⟩ := vandermondeTop c de hc hw
    obtain ⟨_, hR', _, hR2', _⟩ := vandermondeTop c de' hc hw'
    have hb := bp_pos c hc ht
    have hFpos : ∀ d : ℕ → ℝ, IsWord c.k d → ∀ i ∈ Icc 2 (c.k - 1), 0 < c.u d i + c.bp := by
      intro d hd i hi
      have := u_mid_nonneg c d hc hd i hi; linarith
    have hF := Finset.prod_pos (hFpos de hw)
    have hF' := Finset.prod_pos (hFpos de' hw')
    have hFF := prod_le_of_ratio _ _ _ _ (hFpos de hw) (top_ratio_le c de' de hc ht hw' hw)
    have hvp := vthp_small c hc hv ht
    rw [vand_top_decomp c de hc ht, vand_top_decomp c de' hc ht, hR, hR']
    have hRpos : 0 < Rde (c.k - 2) de := lt_of_lt_of_le (Real.exp_pos _) hR1
    refine ⟨by positivity, ?_⟩
    have key := combine
      ((∏ j ∈ Icc 2 (c.k - 1), (c.a - c.u de j)) * ∏ i ∈ Icc 2 (c.k - 1), (c.u de i + c.bp))
      ((∏ j ∈ Icc 2 (c.k - 1), (c.a - c.u de' j)) * ∏ i ∈ Icc 2 (c.k - 1), (c.u de' i + c.bp))
      (c.a - c.ulast) (Rde (c.k - 2) de) (Rde (c.k - 2) de') (Vand (c.k - 2) c.v)
      (Real.exp (1 / 3) * Real.exp (c.vthp / 3)) (Real.exp (((c.k : ℝ) - 1) / 4))
      (Real.exp (-(((c.k : ℝ) - 1) / 4))) (Real.exp ((c.k : ℝ) / 2 + 1))
      (mul_pos hE hF) (mul_pos hE' hF') hC hW (Real.exp_pos _) (Real.exp_pos _)
      (by
        calc _ ≤ (Real.exp (1 / 3) * ∏ j ∈ Icc 2 (c.k - 1), (c.a - c.u de j)) *
              (Real.exp (c.vthp / 3) * ∏ i ∈ Icc 2 (c.k - 1), (c.u de i + c.bp)) :=
              mul_le_mul hEE hFF hF'.le (by positivity)
          _ = _ := by ring)
      hR2' hR1
      (by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith)
    calc _ = _ := by ring
      _ ≤ _ := key
      _ = _ := by ring
  · have ht' : c.top = false := by simpa using ht
    obtain ⟨hW, hR, hR1, _⟩ := vandermondeNonTop c de hc hw ht'
    obtain ⟨_, hR', _, hR2'⟩ := vandermondeNonTop c de' hc hw' ht'
    rw [hR, hR']
    have hRpos : 0 < Rde (c.k - 1) de := lt_of_lt_of_le (Real.exp_pos _) hR1
    refine ⟨by positivity, ?_⟩
    exact combine _ _ _ _ _ _ (Real.exp (1 / 3)) (Real.exp ((c.k : ℝ) / 4))
      (Real.exp (-((c.k : ℝ) / 4))) (Real.exp ((c.k : ℝ) / 2 + 1)) hE hE' hC hW (Real.exp_pos _)
      (Real.exp_pos _) hEE hR2' hR1
      (by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith)

end Formalism.FourierDecayAlt.P.Sz4

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.Sz Formalism.FourierDecayAlt.P.Sz4

theorem vandermondeWords : Formalism.FourierDecayAlt.Sz.VandWords := by
  intro c de de' hc hv hw hw'
  obtain ⟨hpos, hle⟩ := vand_le c de de' hc hv hw hw'
  obtain ⟨hpos', hle'⟩ := vand_le c de' de hc hv hw' hw
  refine ⟨hpos, hpos', ?_⟩
  rw [abs_le]
  constructor
  · rw [Real.le_log_iff_exp_le (div_pos hpos' hpos), le_div_iff₀ hpos, Real.exp_neg,
      inv_mul_le_iff₀ (Real.exp_pos _)]
    exact hle'
  · rw [Real.log_le_iff_le_exp (div_pos hpos' hpos), div_le_iff₀ hpos]
    exact hle

end Formalism.FourierDecayAlt.P
