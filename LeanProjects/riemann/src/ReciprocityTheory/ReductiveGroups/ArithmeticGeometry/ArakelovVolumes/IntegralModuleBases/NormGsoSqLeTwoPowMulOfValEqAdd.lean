import ReciprocityTheory.ReducedBases.LatticeReduction
import ReciprocityTheory.ReducedBases.TBInjective

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases

open Finset InnerProductSpace ReciprocityTheory.ReducedBases.T2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

lemma norm_gso_sq_le_two_pow_mul_of_val_eq_add (b : Fin d → E) (hr : IsRed b) :
    ∀ (n : ℕ) (i j : Fin d), i.val = j.val + n → ‖gs b j‖ ^ 2 ≤ 2 ^ n * ‖gs b i‖ ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro i j h
    have hij : i = j := Fin.ext (by simpa using h)
    subst hij; simp
  | succ n ih =>
    intro i j h
    have hk : j.val + 1 < d := by have := i.isLt; omega
    have h1 := hr.2.2 ⟨j.val + 1, hk⟩ j rfl
    have h2 := ih i ⟨j.val + 1, hk⟩ (by show i.val = j.val + 1 + n; omega)
    calc ‖gs b j‖ ^ 2 ≤ 2 * ‖gs b ⟨j.val + 1, hk⟩‖ ^ 2 := h1
      _ ≤ 2 * (2 ^ n * ‖gs b i‖ ^ 2) := by linarith
      _ = 2 ^ (n + 1) * ‖gs b i‖ ^ 2 := by ring

lemma gs_sq_le_pow (b : Fin d → E) (hr : IsRed b) (i j : Fin d) (h : j ≤ i) :
    ‖gs b j‖ ^ 2 ≤ 2 ^ (i.val - j.val) * ‖gs b i‖ ^ 2 := by
  have h' : j.val ≤ i.val := h
  exact norm_gso_sq_le_two_pow_mul_of_val_eq_add b hr _ i j (by omega)

lemma sum_lt_le (b : Fin d → E) (hr : IsRed b) (i : Fin d) :
    ∑ j ∈ univ.filter (fun j : Fin d => j < i), ‖gs b j‖ ^ 2 ≤
      (2 * 2 ^ i.val - 2) * ‖gs b i‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos
  · have hE : univ.filter (fun j : Fin d => j < i) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro j _; rw [Fin.lt_iff_val_lt_val, h0]; omega
    rw [hE, sum_empty, h0]; simp
  · obtain ⟨n, hn⟩ : ∃ n, i.val = n + 1 := ⟨i.val - 1, by omega⟩
    have hnd : n < d := by have := i.isLt; omega
    have hset : univ.filter (fun j : Fin d => j < i) = univ.filter (fun j : Fin d => j.val ≤ n) := by
      ext j; simp only [mem_filter, mem_univ, true_and, Fin.lt_iff_val_lt_val]; omega
    rw [hset]
    have h1 := sum_gs_le b hr.2.2 n hnd
    have h2 := hr.2.2 i ⟨n, hnd⟩ hn
    have hpow : (2:ℝ) ^ i.val = 2 * 2 ^ n := by rw [hn, pow_succ]; ring
    have hA : (0:ℝ) ≤ 2 ^ (n + 1) - 1 := by
      have : (1:ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
      linarith
    calc _ ≤ (2 ^ (n + 1) - 1) * ‖gs b ⟨n, hnd⟩‖ ^ 2 := h1
      _ ≤ (2 ^ (n + 1) - 1) * (2 * ‖gs b i‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hA
      _ = (2 * 2 ^ i.val - 2) * ‖gs b i‖ ^ 2 := by rw [hpow]; ring

lemma norm_sq_b (b : Fin d → E) (hb : LinearIndependent ℝ b) (i : Fin d) :
    ‖b i‖ ^ 2 = ∑ j, mu b i j ^ 2 * ‖gs b j‖ ^ 2 := by
  have h := norm_sq_comb b hb (fun l => if l = i then (1:ℝ) else 0)
  have hs : ∑ l, (if l = i then (1:ℝ) else 0) • b l = b i := by simp
  have hn : ∀ j, nu b (fun l => if l = i then (1:ℝ) else 0) j = mu b i j := by
    intro j; simp [nu]
  rw [hs] at h; rw [h]; simp only [hn]

lemma norm_sq_le_pow_gs (b : Fin d → E) (hr : IsRed b) (i : Fin d) :
    ‖b i‖ ^ 2 ≤ 2 ^ i.val * ‖gs b i‖ ^ 2 := by
  have hb := hr.1
  rw [norm_sq_b b hb i]
  have hle : ∀ j ∈ (univ : Finset (Fin d)), mu b i j ^ 2 * ‖gs b j‖ ^ 2 ≤
      (if j < i then (1 / 4) * ‖gs b j‖ ^ 2 else 0) + (if j = i then ‖gs b i‖ ^ 2 else 0) := by
    intro j _
    rcases lt_trichotomy j i with h | h | h
    · have hm := hr.2.1 i j h
      have hq : mu b i j ^ 2 ≤ 1 / 4 := by
        nlinarith [abs_nonneg (mu b i j), sq_abs (mu b i j)]
      have := mul_le_mul_of_nonneg_right hq (sq_nonneg ‖gs b j‖)
      simp only [h, h.ne, if_true, if_false, add_zero]
      linarith
    · subst h; simp [mu_self b hb]
    · simp [mu_of_lt b h, h.ne', not_lt.mpr h.le]
  calc _ ≤ ∑ j, ((if j < i then (1 / 4) * ‖gs b j‖ ^ 2 else 0) + (if j = i then ‖gs b i‖ ^ 2 else 0)) :=
        sum_le_sum hle
    _ = (1 / 4) * ∑ j ∈ univ.filter (fun j : Fin d => j < i), ‖gs b j‖ ^ 2 + ‖gs b i‖ ^ 2 := by
        rw [sum_filter, mul_sum, sum_add_distrib]
        congr 1
        · apply sum_congr rfl; intro j _; split_ifs <;> ring
        · simp
    _ ≤ (1 / 4) * ((2 * 2 ^ i.val - 2) * ‖gs b i‖ ^ 2) + ‖gs b i‖ ^ 2 := by
        have := sum_lt_le b hr i; linarith
    _ ≤ 2 ^ i.val * ‖gs b i‖ ^ 2 := by
        have h1 : (1:ℝ) ≤ 2 ^ i.val := one_le_pow₀ (by norm_num)
        nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sq_nonneg ‖gs b i‖)]

lemma gs_sq_ge (b : Fin d → E) (hr : IsRed b) (m : ℝ) (hm : ∀ i, m ≤ ‖b i‖ ^ 2) (j : Fin d) :
    m / 2 ^ (d - 1) ≤ ‖gs b j‖ ^ 2 := by
  have h1 := norm_sq_le_pow_gs b hr j
  have h2 := hm j
  have hjd : j.val ≤ d - 1 := by have := j.isLt; omega
  have hp : (2:ℝ) ^ j.val ≤ 2 ^ (d - 1) := pow_le_pow_right₀ (by norm_num) hjd
  have hpos : (0:ℝ) < 2 ^ (d - 1) := by positivity
  rw [div_le_iff₀ hpos]
  nlinarith [mul_le_mul_of_nonneg_right hp (sq_nonneg ‖gs b j‖)]

theorem red_norm_sq_le (b : Fin d → E) (hr : IsRed b) (m D : ℝ) (hm0 : 0 < m)
    (hm : ∀ i, m ≤ ‖b i‖ ^ 2) (hD : (Matrix.gram ℝ b).det ≤ D) (i : Fin d) :
    ‖b i‖ ^ 2 ≤ 2 ^ (d * (d - 1)) * D / m ^ (d - 1) := by
  have hb := hr.1
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = m / 2 ^ (d - 1) := ⟨_, rfl⟩
  have hLpos : 0 < L := by rw [hL]; positivity
  have hG : ∀ j, L ≤ ‖gs b j‖ ^ 2 := fun j => by rw [hL]; exact gs_sq_ge b hr m hm j
  have hprod : L ^ (d - 1) ≤ ∏ j ∈ univ.erase i, ‖gs b j‖ ^ 2 := by
    have := Finset.prod_le_prod (s := univ.erase i) (f := fun _ => L) (g := fun j => ‖gs b j‖ ^ 2)
      (fun _ _ => hLpos.le) (fun j _ => hG j)
    rw [Finset.prod_const, Finset.card_erase_of_mem (mem_univ i), Finset.card_univ,
      Fintype.card_fin] at this
    exact this
  have hdet : ‖gs b i‖ ^ 2 * ∏ j ∈ univ.erase i, ‖gs b j‖ ^ 2 ≤ D := by
    rw [Finset.mul_prod_erase univ (fun j => ‖gs b j‖ ^ 2) (mem_univ i), ← det_gram_eq b hb]
    exact hD
  have hGi : ‖gs b i‖ ^ 2 * L ^ (d - 1) ≤ D :=
    le_trans (mul_le_mul_of_nonneg_left hprod (sq_nonneg _)) hdet
  have hLp : 0 < L ^ (d - 1) := pow_pos hLpos _
  have hGi' : ‖gs b i‖ ^ 2 ≤ D / L ^ (d - 1) := by rw [le_div_iff₀ hLp]; exact hGi
  have hid : (2:ℝ) ^ i.val ≤ 2 ^ (d - 1) :=
    pow_le_pow_right₀ (by norm_num) (by have := i.isLt; omega)
  have key : D / L ^ (d - 1) = 2 ^ ((d - 1) * (d - 1)) * D / m ^ (d - 1) := by
    rw [hL, div_pow, ← pow_mul, div_div_eq_mul_div]; ring
  have hnat : d * (d - 1) = (d - 1) + (d - 1) * (d - 1) := by
    cases d with
    | zero => rfl
    | succ k => simp only [Nat.add_sub_cancel]; ring
  have hexp : (2:ℝ) ^ (d * (d - 1)) = 2 ^ (d - 1) * 2 ^ ((d - 1) * (d - 1)) := by
    rw [← pow_add, hnat]
  have hDL : 0 ≤ D / L ^ (d - 1) := le_trans (sq_nonneg _) hGi'
  calc ‖b i‖ ^ 2 ≤ 2 ^ i.val * ‖gs b i‖ ^ 2 := norm_sq_le_pow_gs b hr i
    _ ≤ 2 ^ (d - 1) * (D / L ^ (d - 1)) := mul_le_mul hid hGi' (sq_nonneg _) (by positivity)
    _ = 2 ^ (d * (d - 1)) * D / m ^ (d - 1) := by rw [key, hexp]; ring

theorem red_coeff_sq_le (b : Fin d → E) (hr : IsRed b) (m : ℝ) (hm0 : 0 < m)
    (hm : ∀ i, m ≤ ‖b i‖ ^ 2) (c : Fin d → ℝ) (i : Fin d) :
    c i ^ 2 ≤ 9 ^ d * ‖∑ l, c l • b l‖ ^ 2 / m := by
  have hb := hr.1
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ‖∑ l, c l • b l‖ ^ 2 := ⟨_, rfl⟩
  rw [← hX]
  have hX0 : 0 ≤ X := by rw [hX]; exact sq_nonneg _
  have hp : (0:ℝ) < 2 ^ (d - 1) := by positivity
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = X * 2 ^ (d - 1) / m := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; exact div_nonneg (mul_nonneg hX0 hp.le) hm0.le
  have hnu : ∀ j, |nu b c j| ≤ Real.sqrt y := by
    intro j
    apply Real.abs_le_sqrt
    have h1 : nu b c j ^ 2 * ‖gs b j‖ ^ 2 ≤ X := by
      rw [hX, norm_sq_comb b hb c]
      exact Finset.single_le_sum (f := fun j => nu b c j ^ 2 * ‖gs b j‖ ^ 2)
        (fun k _ => by positivity) (mem_univ j)
    have h2 := gs_sq_ge b hr m hm j
    have h3 : nu b c j ^ 2 * (m / 2 ^ (d - 1)) ≤ X :=
      le_trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)) h1
    rw [hy, le_div_iff₀ hm0]
    have h4 : nu b c j ^ 2 * (m / 2 ^ (d - 1)) * 2 ^ (d - 1) = nu b c j ^ 2 * m := by
      rw [mul_assoc, div_mul_cancel₀ _ hp.ne']
    nlinarith [mul_le_mul_of_nonneg_right h3 hp.le]
  have hc := coeff_bound b hb hr.2.1 c (Real.sqrt_nonneg y) hnu i
  have hsq : c i ^ 2 ≤ ((3 / 2 : ℝ) ^ d * Real.sqrt y) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hc 2
  rw [mul_pow, Real.sq_sqrt hy0] at hsq
  have h1 : ((3 / 2 : ℝ) ^ d) ^ 2 * 4 ^ d = 9 ^ d := by
    rw [← pow_mul, mul_comm d 2, pow_mul, ← mul_pow]; norm_num
  have h2 : (2:ℝ) ^ (d - 1) ≤ 4 ^ d :=
    calc (2:ℝ) ^ (d - 1) ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      _ ≤ 4 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hA : ((3 / 2 : ℝ) ^ d) ^ 2 * 2 ^ (d - 1) ≤ 9 ^ d :=
    calc _ ≤ ((3 / 2 : ℝ) ^ d) ^ 2 * 4 ^ d := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 9 ^ d := h1
  calc c i ^ 2 ≤ ((3 / 2 : ℝ) ^ d) ^ 2 * y := hsq
    _ = (((3 / 2 : ℝ) ^ d) ^ 2 * 2 ^ (d - 1)) * X / m := by rw [hy]; ring
    _ ≤ 9 ^ d * X / m := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hA hX0) hm0.le

end ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases

end
