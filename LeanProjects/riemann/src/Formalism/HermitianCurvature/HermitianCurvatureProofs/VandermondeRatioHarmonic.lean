import Formalism.HermitianCurvature.StatementSz

namespace Formalism.FourierDecayAlt.P.Sz3

open Finset Formalism.FourierDecayAlt.Sz

lemma b_lt (c : Cfg) (hc : c.Ok) (j : ℕ) (hj : 1 ≤ j) :
    ∀ j' : ℕ, j < j' → j' ≤ c.m → c.b j < c.b j' := by
  intro j' hjj'
  induction j', hjj' using Nat.le_induction with
  | base =>
    intro h
    have := hc.hgap j hj (by omega)
    linarith
  | succ n hn ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := hc.hgap n (by omega) (by omega)
    linarith

lemma b_ge_one (c : Cfg) (hc : c.Ok) (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ c.m) : 1 ≤ c.b j := by
  rcases Nat.eq_or_lt_of_le hj with h | h
  · rw [← h]; exact hc.hb1
  · have := b_lt c hc 1 le_rfl j h hjm
    linarith [hc.hb1]

end Formalism.FourierDecayAlt.P.Sz3

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.Sz

theorem interlacing : Formalism.FourierDecayAlt.Sz.Interlacing := by
  intro c de hc hw
  obtain ⟨hk, hm, hDel, hv0, hv1, hb1, hgap, ha, htop⟩ := hc
  have hkR : (4 : ℝ) ≤ c.k := by exact_mod_cast hk
  refine ⟨?_, ?_⟩
  · intro i hi1 hik
    have hl : c.lam i = c.v i := by simp [Cfg.lam, hik]
    rw [hl]
    constructor
    · by_cases h1 : i = 1
      · subst h1
        have : c.u de 1 = c.a := by simp [Cfg.u]
        rw [this]; nlinarith
      · have hne : i ≠ c.k := by omega
        have : c.u de i = c.v (i - 1) - 1 / 2 - de (i - 1) * c.Del := by simp [Cfg.u, h1, hne]
        rw [this]
        have hc1 : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
          rw [Nat.cast_sub hi1]; simp
        unfold Cfg.v; rw [hc1]
        rcases hw.1 (i - 1) with h | h <;> rw [h] <;> nlinarith
    · have h1 : i + 1 ≠ 1 := by omega
      by_cases hlast : i + 1 = c.k
      · have : c.u de (i + 1) = c.ulast := by
          unfold Cfg.u; rw [if_neg h1, if_pos hlast]
        rw [this]
        have hiR : (i : ℝ) + 1 = c.k := by exact_mod_cast hlast
        have hvi : c.v i = c.vlast := by unfold Cfg.v; rw [← hiR]; ring
        rw [hvi]; unfold Cfg.ulast
        by_cases ht : c.top = true
        · have := htop ht; simp [ht]; linarith [this.1]
        · simp [ht]
      · have : c.u de (i + 1) = c.v i - 1 / 2 - de i * c.Del := by
          unfold Cfg.u; rw [if_neg h1, if_neg hlast]; simp
        rw [this]
        rcases hw.1 i with h | h <;> rw [h] <;> nlinarith
  · have hl : c.lam c.k = -c.b 1 := by simp [Cfg.lam]
    have hu : c.u de c.k = c.ulast := by
      have : c.k ≠ 1 := by omega
      simp [Cfg.u, this]
    rw [hl, hu]; unfold Cfg.ulast
    by_cases ht : c.top = true
    · have := htop ht; simp [ht]; linarith [this.2]
    · simp [ht]; linarith

theorem lamStrictAnti : Formalism.FourierDecayAlt.Sz.LamAnti := by
  intro c hc s t hs hst ht
  have hDel := hc.hDel
  have hstR : (s : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast hst
  by_cases htk : t < c.k
  · have hsk : s < c.k := by omega
    have h1 : c.lam t = c.v t := by simp [Cfg.lam, htk]
    have h2 : c.lam s = c.v s := by simp [Cfg.lam, hsk]
    rw [h1, h2]; unfold Cfg.v
    nlinarith
  · have h1 : c.lam t = -c.b (t + 1 - c.k) := by simp [Cfg.lam, htk]
    rw [h1]
    by_cases hsk : s < c.k
    · have h2 : c.lam s = c.v s := by simp [Cfg.lam, hsk]
      rw [h2]
      have hb := Sz3.b_ge_one c hc (t + 1 - c.k) (by omega) (by omega)
      have hskR : (s : ℝ) + 1 ≤ (c.k : ℝ) := by exact_mod_cast hsk
      have hv0 := hc.hv0
      unfold Cfg.v
      nlinarith
    · have h2 : c.lam s = -c.b (s + 1 - c.k) := by simp [Cfg.lam, hsk]
      rw [h2]
      have := Sz3.b_lt c hc (s + 1 - c.k) (by omega) (t + 1 - c.k) (by omega) (by omega)
      linarith

theorem positionDiff : Formalism.FourierDecayAlt.Sz.PositionDiff := by
  intro c de hc hw i i' hi hii' hi'k hor
  have h1 : c.u de (i + 1) = c.v i - 1 / 2 - de i * c.Del := by
    unfold Cfg.u
    rw [if_neg (by omega), if_neg (by omega)]; simp
  rw [h1]
  by_cases hlast : i' + 1 = c.k
  · have htop : c.top = false := by
      rcases hor with h | h
      · omega
      · exact h
    have h2 : c.u de (i' + 1) = c.vlast - 1 / 2 := by
      unfold Cfg.u
      rw [if_neg (by omega), if_pos hlast]
      simp [Cfg.ulast, htop]
    have hde : de i' = 0 := by
      have : i' = c.k - 1 := by omega
      rw [this]; exact hw.2
    have hkR : (i' : ℝ) + 1 = (c.k : ℝ) := by exact_mod_cast hlast
    rw [h2, hde]; unfold Cfg.v; rw [← hkR]; ring
  · have h2 : c.u de (i' + 1) = c.v i' - 1 / 2 - de i' * c.Del := by
      unfold Cfg.u
      rw [if_neg (by omega), if_neg hlast]; simp
    rw [h2]; unfold Cfg.v; ring

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.Sz3

open Finset Formalism.FourierDecayAlt.Sz

lemma log_one_add_sub (x : ℝ) (hx : |x| ≤ 1 / 4) : |Real.log (1 + x) - x| ≤ 2 / 3 * x ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -x) (by rw [abs_neg]; linarith) 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at h
  have hy0 : 0 ≤ |x| := abs_nonneg x
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have hB : |x| ^ (3 + 1) / (1 - |x|) ≤ x ^ 2 / 12 := by
    rw [div_le_iff₀ (by linarith)]
    have : |x| ^ (3 + 1) = x ^ 2 * |x| ^ 2 := by rw [← hx2]; ring
    rw [this]
    have h2 : |x| ^ 2 ≤ 1 / 16 := by nlinarith
    have h3 : 0 ≤ x ^ 2 := sq_nonneg x
    nlinarith
  have h' := abs_le.mp (h.trans hB)
  obtain ⟨hxl, hxu⟩ := abs_le.mp hx
  have h3 : 0 ≤ x ^ 2 := sq_nonneg x
  have hc1 : x ^ 3 ≤ x ^ 2 / 4 := by nlinarith
  have hc2 : -(x ^ 2 / 4) ≤ x ^ 3 := by nlinarith
  norm_num at h'
  rw [abs_le]
  constructor <;> nlinarith [h'.1, h'.2]

lemma pair_reindex (J : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ i ∈ Icc 1 J, ∑ i' ∈ Ioc i J, f i i' = ∑ d ∈ Icc 1 J, ∑ i ∈ Icc 1 (J - d), f i (i + d) := by
  have h : ∀ i, ∑ i' ∈ Ioc i J, f i i' = ∑ d ∈ Icc 1 (J - i), f i (i + d) := by
    intro i
    apply Finset.sum_nbij' (fun i' => i' - i) (fun d => i + d)
    · intro a ha; simp only [mem_Ioc, mem_Icc] at *; omega
    · intro a ha; simp only [mem_Ioc, mem_Icc] at *; omega
    · intro a ha; simp only [mem_Ioc] at *; omega
    · intro a ha; simp only [mem_Icc] at *; omega
    · intro a ha
      simp only [mem_Ioc] at ha
      have : i + (a - i) = a := by omega
      rw [this]
  simp_rw [h]
  apply Finset.sum_comm'
  intro i d
  simp only [mem_Icc]
  omega

noncomputable def NF (J : ℕ) (de : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Icc 1 J, (∑ i ∈ Ioc d J, de i - ∑ i ∈ Icc 1 (J - d), de i) / (d : ℝ)

lemma shift_sum (J d : ℕ) (hd : d ≤ J) (de : ℕ → ℝ) :
    ∑ i ∈ Icc 1 (J - d), de (i + d) = ∑ i ∈ Ioc d J, de i := by
  apply Finset.sum_nbij' (fun i => i + d) (fun i => i - d)
  · intro a ha; simp only [mem_Ioc, mem_Icc] at *; omega
  · intro a ha; simp only [mem_Ioc, mem_Icc] at *; omega
  · intro a ha; simp only [mem_Icc] at *; omega
  · intro a ha; simp only [mem_Ioc] at *; omega
  · intro a ha; rfl

lemma pair_eq_NF (J : ℕ) (de : ℕ → ℝ) :
    ∑ i ∈ Icc 1 J, ∑ i' ∈ Ioc i J, (de i' - de i) / (4 * ((i' : ℝ) - (i : ℝ))) =
      (1 / 4) * NF J de := by
  rw [pair_reindex, NF, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [mem_Icc] at hd
  rw [← shift_sum J d hd.2 de, ← Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hd0 : (d : ℝ) ≠ 0 := by
    have : 0 < d := by omega
    positivity
  push_cast
  have : 4 * ((i : ℝ) + d - i) = 4 * d := by ring
  rw [this]
  field_simp

lemma harmonic_real (n : ℕ) : ((harmonic n : ℚ) : ℝ) = ∑ d ∈ Icc 1 n, 1 / (d : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  simp

lemma harm_eq_NF (J : ℕ) (de : ℕ → ℝ) :
    ∑ i ∈ Icc 1 J, de i * (((harmonic (i - 1) : ℚ) : ℝ) - ((harmonic (J - i) : ℚ) : ℝ)) =
      NF J de := by
  simp_rw [harmonic_real, mul_sub, Finset.mul_sum]
  rw [Finset.sum_sub_distrib, NF]
  simp_rw [sub_div, Finset.sum_div]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm' (t' := Icc 1 J) (s' := fun d => Ioc d J)]
    · apply Finset.sum_congr rfl; intro d _; apply Finset.sum_congr rfl; intro i _; ring
    · intro i d; simp only [mem_Icc, mem_Ioc]; omega
  · rw [Finset.sum_comm' (t' := Icc 1 J) (s' := fun d => Icc 1 (J - d))]
    · apply Finset.sum_congr rfl; intro d _; apply Finset.sum_congr rfl; intro i _; ring
    · intro i d; simp only [mem_Icc]; omega

end Formalism.FourierDecayAlt.P.Sz3

namespace Formalism.FourierDecayAlt.P.Sz3

open Finset Formalism.FourierDecayAlt.Sz

noncomputable def hs (n : ℕ) : ℝ := ∑ d ∈ Ioc 0 n, 1 / (d : ℝ)

lemma hs_succ (n : ℕ) : hs (n + 1) = hs n + 1 / ((n : ℝ) + 1) := by
  unfold hs
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]
  push_cast
  rfl

lemma hs_zero : hs 0 = 0 := by simp [hs]

lemma hs_tail (p : ℕ) (hp : 1 ≤ p) : hs (2 * p) - hs p ≤ 7 / 10 - 1 / (4 * (p : ℝ) + 1) := by
  induction p, hp using Nat.le_induction with
  | base =>
    have h2 : hs (2 * 1) = hs 1 + 1 / ((1 : ℝ) + 1) := by
      have := hs_succ 1
      simpa using this
    rw [h2]; norm_num
  | succ n hn ih =>
    have h1 : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
    rw [h1, hs_succ, hs_succ, hs_succ]
    push_cast
    have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have e1 : 1 / ((2 : ℝ) * n + 1) + 1 / (2 * n + 1 + 1) - 1 / (n + 1) =
        1 / ((2 * n + 1) * (2 * n + 2)) := by
      field_simp; ring
    have e2 : 1 / (4 * (n : ℝ) + 1) - 1 / (4 * (n + 1) + 1) = 4 / ((4 * n + 1) * (4 * n + 5)) := by
      field_simp; ring
    have key : 1 / (((2 : ℝ) * n + 1) * (2 * n + 2)) ≤ 4 / ((4 * n + 1) * (4 * n + 5)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

lemma hs_sub (p J : ℕ) (h : p ≤ J) : ∑ d ∈ Ioc p J, 1 / (d : ℝ) = hs J - hs p := by
  unfold hs
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le p) h]
  ring

lemma hs_mono (p J : ℕ) (h : p ≤ J) : hs p ≤ hs J := by
  have := hs_sub p J h
  have h0 : 0 ≤ ∑ d ∈ Ioc p J, 1 / (d : ℝ) := Finset.sum_nonneg (fun d _ => by positivity)
  linarith

lemma sum_de_bd (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) (s : Finset ℕ) :
    0 ≤ ∑ i ∈ s, de i ∧ ∑ i ∈ s, de i ≤ (s.card : ℝ) := by
  constructor
  · apply Finset.sum_nonneg
    intro i _
    rcases hde i with h | h <;> linarith
  · have : ∑ i ∈ s, de i ≤ ∑ _i ∈ s, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rcases hde i with h | h <;> linarith
    simpa using this

lemma Icc_one_eq (n : ℕ) : Icc 1 n = Ioc 0 n := by
  ext x; simp only [mem_Icc, mem_Ioc]; omega

lemma diff_bd (J d : ℕ) (hd : d ≤ J) (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) :
    |∑ i ∈ Ioc d J, de i - ∑ i ∈ Icc 1 (J - d), de i| ≤ (d : ℝ) ∧
    |∑ i ∈ Ioc d J, de i - ∑ i ∈ Icc 1 (J - d), de i| ≤ (J : ℝ) - (d : ℝ) := by
  rw [Icc_one_eq]
  have c1 := Finset.sum_Ioc_consecutive de (Nat.zero_le d) hd
  have c2 := Finset.sum_Ioc_consecutive de (Nat.zero_le (J - d)) (Nat.sub_le J d)
  have b1 := sum_de_bd de hde (Ioc 0 d)
  have b2 := sum_de_bd de hde (Ioc d J)
  have b3 := sum_de_bd de hde (Ioc 0 (J - d))
  have b4 := sum_de_bd de hde (Ioc (J - d) J)
  simp only [Nat.card_Ioc] at b1 b2 b3 b4
  have e1 : ((J - d : ℕ) : ℝ) = (J : ℝ) - d := by rw [Nat.cast_sub hd]
  have e2 : ((J - (J - d) : ℕ) : ℝ) = (d : ℝ) := by
    have : J - (J - d) = d := by omega
    rw [this]
  rw [e1] at b2
  rw [Nat.sub_zero] at b1 b3
  rw [e1] at b3
  rw [e2] at b4
  constructor <;> rw [abs_le] <;> constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2]

lemma NF_bd (J : ℕ) (hJ : 1 ≤ J) (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) :
    |NF J de| ≤ 7 / 10 * (J : ℝ) + 1 := by
  unfold NF
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ : ∃ p : ℕ, 1 ≤ p ∧ p ≤ J ∧ J ≤ 2 * p ∧ 2 * p ≤ J + 1 :=
    ⟨(J + 1) / 2, by omega, by omega, by omega, by omega⟩
  rw [Icc_one_eq J, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le p) hp2]
  have hA : ∑ d ∈ Ioc 0 p, |(∑ i ∈ Ioc d J, de i - ∑ i ∈ Icc 1 (J - d), de i) / (d : ℝ)| ≤
      ∑ _d ∈ Ioc 0 p, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro d hd
    simp only [mem_Ioc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    rw [abs_div, abs_of_pos hd0, div_le_one hd0]
    exact (diff_bd J d (by omega) de hde).1
  have hB : ∑ d ∈ Ioc p J, |(∑ i ∈ Ioc d J, de i - ∑ i ∈ Icc 1 (J - d), de i) / (d : ℝ)| ≤
      ∑ d ∈ Ioc p J, ((J : ℝ) * (1 / (d : ℝ)) - 1) := by
    apply Finset.sum_le_sum
    intro d hd
    simp only [mem_Ioc] at hd
    have hd0 : (0 : ℝ) < d := by
      have : 0 < d := by omega
      exact_mod_cast this
    rw [abs_div, abs_of_pos hd0, div_le_iff₀ hd0]
    have := (diff_bd J d hd.2 de hde).2
    have e : ((J : ℝ) * (1 / (d : ℝ)) - 1) * d = J - d := by field_simp
    rw [e]; exact this
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hs_sub p J hp2] at hB
  simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one, Nat.sub_zero] at hA hB
  rw [Nat.cast_sub hp2] at hB
  have ht := hs_tail p hp1
  have hm := hs_mono J (2 * p) hp3
  have hpos : (0 : ℝ) < 1 / (4 * (p : ℝ) + 1) := by positivity
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have h7 : hs J - hs p ≤ 7 / 10 := by linarith
  have hmul : (J : ℝ) * (hs J - hs p) ≤ J * (7 / 10) := mul_le_mul_of_nonneg_left h7 hJ0
  have hp4R : 2 * (p : ℝ) ≤ J + 1 := by exact_mod_cast hp4
  linarith

lemma sum_inv_sq (n : ℕ) : ∑ d ∈ Icc 1 n, 1 / (d : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 :=
  sum_le_hasSum _ (fun i _ => by positivity) hasSum_zeta_two

noncomputable def xx (de : ℕ → ℝ) (i i' : ℕ) : ℝ := (de i' - de i) / (4 * ((i' : ℝ) - (i : ℝ)))

lemma xx_bd (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) (i i' : ℕ) (h : i < i') :
    |xx de i i'| ≤ 1 / 4 ∧ (xx de i i') ^ 2 ≤ 1 / 16 * (1 / (((i' - i : ℕ) : ℝ)) ^ 2) := by
  have hR : (i : ℝ) + 1 ≤ (i' : ℝ) := by exact_mod_cast h
  have hc : ((i' - i : ℕ) : ℝ) = (i' : ℝ) - i := by rw [Nat.cast_sub h.le]
  have hpos : (0 : ℝ) < (i' : ℝ) - i := by linarith
  have hnum : |de i' - de i| ≤ 1 := by
    rcases hde i with h1 | h1 <;> rcases hde i' with h2 | h2 <;> rw [h1, h2] <;> norm_num
  constructor
  · unfold xx
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * ((i' : ℝ) - i)),
      div_le_iff₀ (by positivity)]
    linarith
  · unfold xx
    rw [hc, div_pow, mul_pow, ← sq_abs (de i' - de i)]
    have : |de i' - de i| ^ 2 ≤ 1 := by
      have h0 := abs_nonneg (de i' - de i)
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    have e : 1 / 16 * (1 / ((i' : ℝ) - i) ^ 2) * (4 ^ 2 * ((i' : ℝ) - i) ^ 2) = 1 := by
      field_simp; norm_num
    rw [e]; exact this

end Formalism.FourierDecayAlt.P.Sz3

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.Sz Sz3

theorem vandermondeRatioHarmonic : Formalism.FourierDecayAlt.Sz.HarmonicVand := by
  intro J de hJ hde
  have hfac : ∀ i i' : ℕ, i < i' → 0 < 1 + xx de i i' := by
    intro i i' h
    have := abs_le.mp (xx_bd de hde i i' h).1
    linarith [this.1]
  have hR : Rde J de = ∏ i ∈ Icc 1 J, ∏ i' ∈ Ioc i J, (1 + xx de i i') := rfl
  have hpos : 0 < Rde J de := by
    rw [hR]
    apply Finset.prod_pos; intro i _
    apply Finset.prod_pos; intro i' hi'
    exact hfac i i' (mem_Ioc.mp hi').1
  have hlog : Real.log (Rde J de) = ∑ i ∈ Icc 1 J, ∑ i' ∈ Ioc i J, Real.log (1 + xx de i i') := by
    rw [hR, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro i _
      rw [Real.log_prod]
      intro i' hi'
      exact (hfac i i' (mem_Ioc.mp hi').1).ne'
    · intro i _
      apply ne_of_gt
      apply Finset.prod_pos; intro i' hi'
      exact hfac i i' (mem_Ioc.mp hi').1
  have hM : ∑ i ∈ Icc 1 J, ∑ i' ∈ Ioc i J, xx de i i' = (1 / 4) * NF J de := pair_eq_NF J de
  have hE : |Real.log (Rde J de) - (1 / 4) * NF J de| ≤ Real.pi ^ 2 / 144 * J := by
    rw [hlog, ← hM, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ i ∈ Icc 1 J, |∑ i' ∈ Ioc i J, Real.log (1 + xx de i i') - ∑ i' ∈ Ioc i J, xx de i i'| ≤
        Real.pi ^ 2 / 144 := by
      intro i _
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h1 : ∑ i' ∈ Ioc i J, |Real.log (1 + xx de i i') - xx de i i'| ≤
          ∑ i' ∈ Ioc i J, 1 / 24 * (1 / (((i' - i : ℕ) : ℝ)) ^ 2) := by
        apply Finset.sum_le_sum
        intro i' hi'
        have hb := xx_bd de hde i i' (mem_Ioc.mp hi').1
        have := log_one_add_sub _ hb.1
        linarith [hb.2]
      have h2 : ∑ i' ∈ Ioc i J, 1 / 24 * (1 / (((i' - i : ℕ) : ℝ)) ^ 2) =
          1 / 24 * ∑ d ∈ Icc 1 (J - i), 1 / (d : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_nbij' (fun i' => i' - i) (fun d => i + d)
        · intro a ha; simp only [mem_Ioc, mem_Icc] at *; omega
        · intro a ha; simp only [mem_Ioc, mem_Icc] at *; omega
        · intro a ha; simp only [mem_Ioc] at *; omega
        · intro a ha; simp only [mem_Icc] at *; omega
        · intro a ha; rfl
      have h3 := sum_inv_sq (J - i)
      linarith
    have h4 := Finset.sum_le_sum this
    simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel] at h4
    linarith
  refine ⟨hpos, ?_, ?_⟩
  · rw [harm_eq_NF]; exact hE
  · have hN := NF_bd J hJ de hde
    have hpi : Real.pi ^ 2 ≤ 10.8 := by
      have h1 := Real.pi_lt_d2
      have h0 := Real.pi_pos
      nlinarith
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have hE' := abs_le.mp hE
    have hN' := abs_le.mp hN
    have hpJ : Real.pi ^ 2 / 144 * J ≤ 10.8 / 144 * J := by
      apply mul_le_mul_of_nonneg_right _ hJ0
      linarith
    rw [abs_le]
    constructor <;> linarith [hE'.1, hE'.2, hN'.1, hN'.2]

end Formalism.FourierDecayAlt.P
