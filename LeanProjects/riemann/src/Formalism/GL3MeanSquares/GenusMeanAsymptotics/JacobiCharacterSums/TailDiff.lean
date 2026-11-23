import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf

open Finset ArithmeticFunction

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

lemma tail_diff_split (g : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Icc 1 b, g n = ∑ n ∈ Icc 1 a, g n + ∑ n ∈ Ioc a b, g n := by
  have h1 : Icc 1 b = Icc 1 a ∪ Ioc a b := by
    ext n
    simp only [mem_union, mem_Icc, mem_Ioc]
    omega
  rw [h1, sum_union]
  rw [disjoint_left]
  intro n h2 h3
  simp only [mem_Icc, mem_Ioc] at h2 h3
  omega

lemma tail_diff_identity {N : ℕ} (χ : DirichletCharacter ℂ N) (z h : ℝ) (hh : 0 < h) :
    Formalism.ZeroFreeDirichlet.Schi χ (z + h) - Formalism.ZeroFreeDirichlet.Schi χ z -
              (h : ℂ) * ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) / (n : ℂ)
      = ∑ n ∈ Ioc ⌊z⌋₊ ⌊z + h⌋₊,
          ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * (((z + h) / n - 1 : ℝ) : ℂ) := by
  unfold Formalism.ZeroFreeDirichlet.Schi
  have hmono : ⌊z⌋₊ ≤ ⌊z + h⌋₊ := Nat.floor_le_floor (by linarith)
  rw [tail_diff_split _ hmono]
  have key : ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * (((z + h) / n - 1 : ℝ) : ℂ)
      - ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((z / n - 1 : ℝ) : ℂ)
      - (h : ℂ) * ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) / (n : ℂ) = 0 := by
    rw [← sum_sub_distrib, mul_sum, ← sum_sub_distrib]
    apply sum_eq_zero
    intro n _
    push_cast
    ring
  linear_combination key

lemma tail_diff_term {N : ℕ} (χ : DirichletCharacter ℂ N) (z h : ℝ) (hz : 1 ≤ z) (hh : 0 < h)
    {n : ℕ} (hn : n ∈ Ioc ⌊z⌋₊ ⌊z + h⌋₊) :
    ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * (((z + h) / n - 1 : ℝ) : ℂ)‖ ≤
      Real.log (z + h) * (h / z) := by
  rw [mem_Ioc] at hn
  have hzpos : 0 < z := by linarith
  have hzn : z < n := Nat.lt_of_floor_lt hn.1
  have hnzh : (n : ℝ) ≤ z + h := (Nat.le_floor_iff (by linarith)).1 hn.2
  have hnpos : (0:ℝ) < n := by linarith
  have hlog : 0 ≤ Real.log (z + h) := Real.log_nonneg (by linarith)
  have hΛ : (Λ n : ℝ) ≤ Real.log (z + h) :=
    vonMangoldt_le_log.trans (Real.log_le_log hnpos hnzh)
  have hΛ0 : 0 ≤ (Λ n : ℝ) := vonMangoldt_nonneg
  have hχ : ‖χ (n : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have ht0 : 0 ≤ (z + h) / n - 1 := by
    rw [sub_nonneg, le_div_iff₀ hnpos]
    linarith
  have ht1 : (z + h) / n - 1 ≤ h / z := by
    rw [div_sub_one hnpos.ne', div_le_div_iff₀ hnpos hzpos]
    nlinarith [mul_pos hh (sub_pos.2 hzn), mul_pos hzpos (sub_pos.2 hzn)]
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hΛ0,
    Real.norm_of_nonneg ht0]
  have e1 : (Λ n : ℝ) * ‖χ (n : ZMod N)‖ ≤ Real.log (z + h) := by
    calc (Λ n : ℝ) * ‖χ (n : ZMod N)‖ ≤ Real.log (z + h) * 1 :=
          mul_le_mul hΛ hχ (norm_nonneg _) hlog
      _ = _ := mul_one _
  exact mul_le_mul e1 ht1 ht0 hlog

theorem tail_diff_schi {N : ℕ} (χ : DirichletCharacter ℂ N) (z h : ℝ) (hz : 1 ≤ z) (hh : 0 < h) :
    ‖Formalism.ZeroFreeDirichlet.Schi χ (z + h) - Formalism.ZeroFreeDirichlet.Schi χ z -
              (h : ℂ) * ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) / (n : ℂ)‖ ≤
      h * (h + 1) * Real.log (z + h) / z := by
  rw [tail_diff_identity χ z h hh]
  have hzpos : 0 < z := by linarith
  have hlog : 0 ≤ Real.log (z + h) := Real.log_nonneg (by linarith)
  have hmono : ⌊z⌋₊ ≤ ⌊z + h⌋₊ := Nat.floor_le_floor (by linarith)
  have hcard : ((Ioc ⌊z⌋₊ ⌊z + h⌋₊).card : ℝ) ≤ h + 1 := by
    rw [Nat.card_Ioc, Nat.cast_sub hmono]
    have h1 : (⌊z + h⌋₊ : ℝ) ≤ z + h := Nat.floor_le (by linarith)
    have h2 : z < ⌊z⌋₊ + 1 := Nat.lt_floor_add_one z
    linarith
  calc _ ≤ ∑ n ∈ Ioc ⌊z⌋₊ ⌊z + h⌋₊, Real.log (z + h) * (h / z) :=
        (norm_sum_le _ _).trans (sum_le_sum fun n hn => tail_diff_term χ z h hz hh hn)
    _ = ((Ioc ⌊z⌋₊ ⌊z + h⌋₊).card : ℝ) * (Real.log (z + h) * (h / z)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (h + 1) * (Real.log (z + h) * (h / z)) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hlog (div_nonneg hh.le hzpos.le))
    _ = h * (h + 1) * Real.log (z + h) / z := by ring

end Formalism.HermitianLattices.Ext.BoxTail
