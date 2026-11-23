import Formalism.LandauZeroFreeBounds.SiegelWalfiszAP
import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf

open Finset Complex ArithmeticFunction

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

lemma sharp_split (g : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Icc 1 b, g n = ∑ n ∈ Icc 1 a, g n + ∑ n ∈ Ioc a b, g n := by
  have hd : Disjoint (Icc 1 a) (Ioc a b) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hx hx'
    omega
  have hu : Icc 1 b = Icc 1 a ∪ Ioc a b := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
    omega
  rw [hu, Finset.sum_union hd]

lemma sharp_schi_div {N : ℕ} (χ : DirichletCharacter ℂ N) {v : ℝ} (hv : 0 < v) :
    Formalism.ZeroFreeDirichlet.Schi χ v / (v : ℂ) =
      ∑ n ∈ Icc 1 ⌊v⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((1 / n - 1 / v : ℝ) : ℂ) := by
  rw [Formalism.ZeroFreeDirichlet.Schi.eq_1, Finset.sum_div]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hv0 : v ≠ 0 := hv.ne'
  rw [mul_div_assoc]
  congr 1
  rw [← Complex.ofReal_div]
  congr 1
  field_simp

lemma sharp_identity {N : ℕ} (χ : DirichletCharacter ℂ N) {y u : ℝ} (hy : 1 ≤ y) (hu : y < u) :
    ((y * u / (u - y) : ℝ) : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ u / (u : ℂ) - Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ)) - psiChi χ y =
      ∑ n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) *
        ((y * u / (u - y) * (1 / n - 1 / u) : ℝ) : ℂ) := by
  have hy0 : 0 < y := by linarith
  have hu0 : 0 < u := by linarith
  have huy : u - y ≠ 0 := (sub_pos.mpr hu).ne'
  have hfl : ⌊y⌋₊ ≤ ⌊u⌋₊ := Nat.floor_mono hu.le
  rw [sharp_schi_div χ hu0, sharp_schi_div χ hy0, sharp_split _ hfl, Formalism.ZeroFreeDirichlet.psiChi.eq_1]
  have hc1 : y * u / (u - y) * (1 / y - 1 / u) = 1 := by
    field_simp
  have hAC : (∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((1 / n - 1 / u : ℝ) : ℂ)) -
      ∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((1 / n - 1 / y : ℝ) : ℂ) =
      ((1 / y - 1 / u : ℝ) : ℂ) * ∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    push_cast
    ring
  have hE : ∑ n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) *
        ((y * u / (u - y) * (1 / n - 1 / u) : ℝ) : ℂ) =
      ((y * u / (u - y) : ℝ) : ℂ) *
        ∑ n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((1 / n - 1 / u : ℝ) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    push_cast
    ring
  have hc1' : ((y * u / (u - y) : ℝ) : ℂ) * ((1 / y - 1 / u : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hc1, Complex.ofReal_one]
  rw [hE]
  linear_combination ((y * u / (u - y) : ℝ) : ℂ) * hAC +
    (∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)) * hc1'

lemma sharp_term {N : ℕ} (χ : DirichletCharacter ℂ N) {y u : ℝ} (hy : 1 ≤ y) (hu : y < u)
    {n : ℕ} (hn : n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊) :
    ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((y * u / (u - y) * (1 / n - 1 / u) : ℝ) : ℂ)‖ ≤
      Real.log u := by
  have hy0 : 0 < y := by linarith
  have hu0 : 0 < u := by linarith
  obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
  have hyn : y < n := (Nat.floor_lt hy0.le).mp hn1
  have hnu : (n : ℝ) ≤ u := (Nat.le_floor_iff hu0.le).mp hn2
  have hnpos : (0:ℝ) < n := by linarith
  have huy : 0 < u - y := by linarith
  have hf0 : 0 ≤ y * u / (u - y) * (1 / n - 1 / u) := by
    apply mul_nonneg (div_nonneg (by positivity) huy.le)
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hnpos hnu
  have hf1 : y * u / (u - y) * (1 / n - 1 / u) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one huy]
    have h1 : y * u * (1 / n - 1 / u) = y * u / n - y := by
      rw [mul_sub, mul_one_div, mul_one_div, mul_div_cancel_right₀ y hu0.ne']
    rw [h1]
    have h2 : y * u / n ≤ u := by
      rw [div_le_iff₀ hnpos]
      nlinarith
    linarith
  have hΛ0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have hΛ : Λ n ≤ Real.log u :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hnpos hnu)
  have hχ : ‖χ (n : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ (n : ZMod N)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg hΛ0, ← abs_mul, abs_of_nonneg hf0]
  calc Λ n * ‖χ (n : ZMod N)‖ * (y * u / (u - y) * (1 / n - 1 / u)) ≤ Λ n * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hχ hΛ0) hf1 hf0 (mul_nonneg hΛ0 zero_le_one)
    _ = Λ n := by ring
    _ ≤ Real.log u := hΛ

theorem sharp_arith {N : ℕ} (χ : DirichletCharacter ℂ N) {y u : ℝ} (hy : 1 ≤ y) (hu : y < u) :
    ‖((y * u / (u - y) : ℝ) : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ u / (u : ℂ) - Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ)) - psiChi χ y‖ ≤
      (u - y + 1) * Real.log u := by
  rw [sharp_identity χ hy hu]
  have hu1 : 1 ≤ u := by linarith
  have hlog : 0 ≤ Real.log u := Real.log_nonneg hu1
  calc _ ≤ ∑ n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod N) *
          ((y * u / (u - y) * (1 / n - 1 / u) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, Real.log u := Finset.sum_le_sum (fun n hn => sharp_term χ hy hu hn)
    _ = ((⌊u⌋₊ - ⌊y⌋₊ : ℕ) : ℝ) * Real.log u := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    _ ≤ (u - y + 1) * Real.log u := by
        apply mul_le_mul_of_nonneg_right _ hlog
        have h1 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le (by linarith)
        have h2 : y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one y
        have h3 : ⌊y⌋₊ ≤ ⌊u⌋₊ := Nat.floor_mono hu.le
        rw [Nat.cast_sub h3]
        linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
