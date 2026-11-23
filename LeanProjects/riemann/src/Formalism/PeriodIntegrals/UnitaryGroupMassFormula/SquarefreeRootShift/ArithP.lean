import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootShift.SumLeProdOfTwoLe

open Finset

noncomputable section

namespace PI.SqfRootShift.W

theorem geom_part (G : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    ∑ k ∈ Finset.Ioc 1 r, (G - 1) * G ^ (r - k) = G ^ (r - 1) - 1 := by
  induction r, hr using Nat.le_induction with
  | base => simp
  | succ r hr ih =>
    rw [Finset.sum_Ioc_succ_top (by omega : 1 ≤ r), Nat.sub_self, pow_zero, mul_one]
    have h : ∑ k ∈ Finset.Ioc 1 r, (G - 1) * G ^ (r + 1 - k) =
        G * ∑ k ∈ Finset.Ioc 1 r, (G - 1) * G ^ (r - k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Ioc] at hk
      rw [show r + 1 - k = (r - k) + 1 by omega, pow_succ]; ring
    rw [h, ih, show r + 1 - 1 = (r - 1) + 1 by omega, pow_succ]; ring

theorem harm_tail (r : ℕ) (hr : 1 ≤ r) : ∑ k ∈ Finset.Ioc 1 r, ((k : ℝ))⁻¹ ≤ Real.log r := by
  have h := harmonic_le_one_add_log r
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  rw [← Finset.add_sum_erase _ _ (Finset.left_mem_Icc.mpr hr), Finset.Icc_erase_left,
    Nat.cast_one, inv_one] at h
  linarith

theorem arithP : ArithP := by
  intro g r q d e hg hq hd hq8 hd16 he hq16 hd16' hgm hr hg12
  have hL : 4 * 2 ^ e * q * d ∣ g - 1 := by
    have := Nat.dvd_sub_mod (n := 4 * 2 ^ e * q * d) g
    rwa [hgm] at this
  have h16L : 16 ∣ 4 * 2 ^ e * q * d := by
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
    exact ⟨2 ^ e' * q * d, by ring⟩
  have h16 : 16 ∣ g - 1 := h16L.trans hL
  have hqg : q ∣ g - 1 := (Dvd.intro (4 * 2 ^ e * d) (by ring)).trans hL
  have hdg : d ∣ g - 1 := (Dvd.intro_left (4 * 2 ^ e * q) rfl).trans hL
  have h4 : 4 ∣ g - 1 := (by norm_num : 4 ∣ 16).trans h16
  have hqd : q ≠ d := by omega
  have hg4096 : 4096 ≤ g := by simpa using hg12
  have hg2 : 2 ≤ g := by omega
  have hA1 := arith1 (n := g - 1) (by omega) hq hd hqd hq16 hd16' h16 hqg hdg
  have hm16 : 16 ≤ min q d := le_min hq16 hd16'
  generalize min q d = m at hA1 hm16 ⊢
  set G : ℝ := (g : ℝ) with hGdef
  have hG : (4096 : ℝ) ≤ G := by rw [hGdef]; exact_mod_cast hg4096
  have hG0 : (0 : ℝ) < G := by linarith
  have hG1 : (0 : ℝ) < G - 1 := by linarith
  have hm : (16 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm16
  have hA1r : 4 * (m : ℝ) * (ppSum (g - 1) : ℝ) ≤ G - 1 := by
    have := (Nat.cast_le (α := ℝ)).mpr hA1
    push_cast [Nat.cast_sub (by omega : 1 ≤ g)] at this
    exact this
  have hP0 : (0 : ℝ) ≤ (ppSum (g - 1) : ℝ) := Nat.cast_nonneg _
  have hP : (ppSum (g - 1) : ℝ) ≤ G - 1 := by nlinarith
  have hA2r : ∀ k : ℕ, 1 ≤ k →
      (ppSum (g ^ k - 1) : ℝ) ≤ k * (ppSum (g - 1) : ℝ) + (G ^ k - 1) / (G - 1) := by
    intro k hk
    have h := arith2 hg2 h4 (k := k) (by omega)
    have hS : (((g ^ k - 1) / (g - 1) : ℕ) : ℝ) = (G ^ k - 1) / (G - 1) := by
      rw [eq_div_iff hG1.ne']
      have hdvd : g - 1 ∣ g ^ k - 1 := by simpa using Nat.sub_dvd_pow_sub_pow g 1 k
      have h1 := Nat.div_mul_cancel hdvd
      have hc := congrArg (fun x : ℕ => (x : ℝ)) h1
      have hgk : 1 ≤ g ^ k := Nat.one_le_pow _ _ (by omega)
      push_cast [Nat.cast_sub (by omega : 1 ≤ g), Nat.cast_sub hgk] at hc
      exact hc
    have hc := (Nat.cast_le (α := ℝ)).mpr h
    push_cast at hc
    rw [hS] at hc
    exact hc
  have hterm : ∀ k ∈ Finset.Ioc 1 r, (ppSum (g ^ k - 1) : ℝ) / k * G ^ (r - k) ≤
      (G - 1) * G ^ (r - k) + G ^ r / (G - 1) * ((k : ℝ))⁻¹ := by
    intro k hk
    rw [Finset.mem_Ioc] at hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hB : (0 : ℝ) ≤ G ^ (r - k) := pow_nonneg hG0.le _
    have h1 : (ppSum (g ^ k - 1) : ℝ) / k ≤ (ppSum (g - 1) : ℝ) + (G ^ k - 1) / (G - 1) / k := by
      rw [div_le_iff₀ hk0, add_mul, div_mul_cancel₀ _ hk0.ne']
      have := hA2r k (by omega)
      linarith
    have hAB : (G ^ k - 1) * G ^ (r - k) ≤ G ^ r := by
      have : G ^ k * G ^ (r - k) = G ^ r := by rw [← pow_add]; congr 1; omega
      nlinarith
    calc (ppSum (g ^ k - 1) : ℝ) / k * G ^ (r - k)
        ≤ ((ppSum (g - 1) : ℝ) + (G ^ k - 1) / (G - 1) / k) * G ^ (r - k) :=
          mul_le_mul_of_nonneg_right h1 hB
      _ = (ppSum (g - 1) : ℝ) * G ^ (r - k) + ((G ^ k - 1) * G ^ (r - k)) / (G - 1) * ((k : ℝ))⁻¹ := by
          ring
      _ ≤ (G - 1) * G ^ (r - k) + G ^ r / (G - 1) * ((k : ℝ))⁻¹ :=
          add_le_add (mul_le_mul_of_nonneg_right hP hB)
            (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hAB hG1.le) (by positivity))
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, geom_part G r (by omega), ← Finset.mul_sum] at hsum
  have hharm := harm_tail r (by omega)
  have hGr0 : (0 : ℝ) ≤ G ^ r / (G - 1) := div_nonneg (pow_nonneg hG0.le _) hG1.le
  have hh := mul_le_mul_of_nonneg_left hharm hGr0
  have hGr : G ^ r = G * G ^ (r - 1) := by rw [← pow_succ']; congr 1; omega
  have hgeo : G ^ (r - 1) - 1 ≤ G ^ r / (G - 1) := by
    rw [le_div_iff₀ hG1, hGr]
    nlinarith [pow_nonneg hG0.le (r - 1)]
  have t1 : (ppSum (g - 1) : ℝ) * G ^ (r - 1) ≤ G ^ r / (4 * (m : ℝ)) := by
    rw [le_div_iff₀ (by positivity), hGr]
    nlinarith [mul_le_mul_of_nonneg_right hA1r (pow_nonneg hG0.le (r - 1)),
      pow_nonneg hG0.le (r - 1)]
  rw [← Finset.add_sum_erase _ _ (Finset.left_mem_Icc.mpr (by omega : 1 ≤ r)),
    Finset.Icc_erase_left]
  simp only [pow_one, Nat.cast_one, div_one]
  have hR : (1 / (4 * (m : ℝ)) + (1 + Real.log r) / (G - 1)) * G ^ r =
      G ^ r / (4 * (m : ℝ)) + G ^ r / (G - 1) + G ^ r / (G - 1) * Real.log r := by ring
  rw [hR]
  linarith

end PI.SqfRootShift.W
