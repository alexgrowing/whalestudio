import Formalism.LandauZeroFreeBounds.NoZeroComplexOf

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma re_one_div_sub_zero_pos {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (σ t : ℝ) (hσ : 1 < σ) :
    0 < (1 / ((σ : ℂ) + t * I - ρ)).re := by
  have hre : ρ.re < 1 := by
    by_contra hc
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (Or.inl hχ) (not_lt.mp hc) hρ
  have hwre : ((σ : ℂ) + t * I - ρ).re = σ - ρ.re := by simp
  have hw0 : (σ : ℂ) + t * I - ρ ≠ 0 := fun h => by
    have h' : ((σ : ℂ) + t * I - ρ).re = 0 := by rw [h, Complex.zero_re]
    linarith
  rw [one_div, Complex.inv_re]
  exact div_pos (by rw [hwre]; linarith) (Complex.normSq_pos.mpr hw0)

lemma re_one_div_ofReal_add_mul_I (x y : ℝ) :
    (1 / ((x : ℂ) + y * I)).re = x / (x ^ 2 + y ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_add_mul_I]
  simp

lemma two_le_mul_abs_add_two (q : ℕ) [NeZero q] (t : ℝ) : 2 ≤ (q : ℝ) * (|t| + 2) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  nlinarith [abs_nonneg t]

lemma log_mul_abs_two_mul_le (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log ((q : ℝ) * (|2 * t| + 2)) ≤ 2 * Real.log ((q : ℝ) * (|t| + 2)) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have ht := abs_nonneg t
  have e : 2 * Real.log ((q : ℝ) * (|t| + 2)) = Real.log (((q : ℝ) * (|t| + 2)) ^ 2) := by
    rw [Real.log_pow]
    norm_num
  rw [abs_mul, abs_two, e]
  apply Real.log_le_log (by positivity)
  have h1 : (q : ℝ) * (2 * |t| + 2) ≤ (q : ℝ) * (|t| + 2) ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have h2 : (q : ℝ) * (|t| + 2) ^ 2 ≤ ((q : ℝ) * (|t| + 2)) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  linarith

theorem realCharZeroFreeLargeHeightOfBounds : RealLargeTOf := by
  intro hLZ hLD hPos hTriv δ hδ
  obtain ⟨C₁, hC₁⟩ := hLZ
  obtain ⟨C₂, hC₂0, hC₂⟩ := hLD
  obtain ⟨C₃, hC₃⟩ := hTriv
  have hM₁ : 0 ≤ max C₁ 0 := le_max_right _ _
  have hM₃ : 0 ≤ max C₃ 0 := le_max_right _ _
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 4 * max C₁ 0 + 2 * max C₃ 0 + 6 * C₂ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = min (δ / 2) (min (1 / 10) (1 / (4 * K + 1))) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; exact lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have ha1 : a ≤ δ / 2 := by rw [ha]; exact min_le_left _ _
  have ha2 : a ≤ 1 / 10 := by rw [ha]; exact (min_le_right _ _).trans (min_le_left _ _)
  have ha3 : a ≤ 1 / (4 * K + 1) := by rw [ha]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hKa : K * a ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at ha3
    nlinarith
  have hδa : a ^ 2 / (4 * δ ^ 2) ≤ 1 / 16 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨a / 8, by positivity, ?_⟩
  intro q _ χ s hχ2 hχ1 hδt hreg hzero
  have hreg' : 1 - a / 8 / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re := hreg
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log ((q : ℝ) * (|s.im| + 2)) := ⟨_, rfl⟩
  rw [← hLdef] at hreg' hδt
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hL : 1 / 2 < L := by
    rw [hLdef]
    exact lt_of_lt_of_le hlog2 (Real.log_le_log (by norm_num) (two_le_mul_abs_add_two q s.im))
  have hLpos : 0 < L := by linarith
  have hβ1 : s.re < 1 := by
    by_contra hc
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (Or.inl hχ1) (not_lt.mp hc)
      hzero
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = 1 + a / L := ⟨_, rfl⟩
  have haL : 0 < a / L := div_pos ha0 hLpos
  have haL5 : a / L ≤ 1 / 5 := by
    rw [div_le_iff₀ hLpos]
    linarith
  have hσ1 : 1 < σ := by linarith
  have hσ65 : σ ≤ 6 / 5 := by linarith
  have ha8 : a / 8 / L = (a / L) / 8 := by ring
  have hσβ : σ - s.re ≤ 9 / 8 * (a / L) := by linarith
  have hσβpos : 0 < σ - s.re := by linarith
  obtain ⟨Z, m, hZ, hm1, -, hbd⟩ := hC₁ q χ hχ1 s.im
  have hsZ : s ∈ Z := by
    rw [hZ]
    refine ⟨?_, hzero⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hd : s - ((11 / 10 : ℂ) + s.im * I) = ((s.re - 11 / 10 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [hd, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have : a / L / 8 ≤ 1 / 40 := by linarith
    constructor <;> linarith
  have hterm : ∀ ρ ∈ Z, 0 ≤ (m ρ : ℝ) * (1 / ((σ : ℂ) + s.im * I - ρ)).re := fun ρ hρ =>
    mul_nonneg (Nat.cast_nonneg _)
      (re_one_div_sub_zero_pos χ hχ1 ρ ((hZ ρ).mp hρ).2 σ s.im hσ1).le
  have hs_term : (1 / ((σ : ℂ) + s.im * I - s)).re = 1 / (σ - s.re) := by
    have hd : (σ : ℂ) + s.im * I - s = ((σ - s.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [hd, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have hsum : 1 / (σ - s.re) ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + s.im * I - ρ)).re := by
    refine le_trans ?_ (Finset.single_le_sum hterm hsZ)
    rw [hs_term]
    have h1 : (1 : ℝ) ≤ m s := by exact_mod_cast hm1 s hsZ
    have h0 : 0 ≤ 1 / (σ - s.re) := by positivity
    nlinarith
  have hu : 8 / 9 * (L / a) ≤ 1 / (σ - s.re) := by
    have h1 := one_div_le_one_div_of_le hσβpos hσβ
    have e : 1 / (9 / 8 * (a / L)) = 8 / 9 * (L / a) := by field_simp
    rw [e] at h1
    exact h1
  have hP := (hPos q σ hσ1).1 χ s.im
  rw [hχ2] at hP
  have h1 : (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re ≤ L / a + C₂ := by
    have h := hC₂ q 1 (σ : ℂ) (by simpa using hσ1)
    have e : 1 / ((σ : ℂ).re - 1) = L / a := by
      rw [Complex.ofReal_re, hσ, add_sub_cancel_left, one_div_div]
    rw [e] at h
    exact (Complex.re_le_norm _).trans h
  have h2 := hbd σ hσ1 hσ65
  rw [← hLdef] at h2
  have h3 := hC₃ q σ (2 * s.im) hσ1 (by linarith)
  have hpole := re_one_div_ofReal_add_mul_I (σ - 1) (2 * s.im)
  push_cast at h3 hpole
  rw [hpole] at h3
  have ht2 : δ ^ 2 / L ^ 2 ≤ s.im ^ 2 := by
    have h0 : 0 ≤ δ / L := by positivity
    have h := pow_le_pow_left₀ h0 hδt 2
    rwa [div_pow, sq_abs] at h
  have hσ1' : σ - 1 = a / L := by rw [hσ]; ring
  have hpb : (σ - 1) / ((σ - 1) ^ 2 + (2 * s.im) ^ 2) ≤ a * L / (4 * δ ^ 2) := by
    rw [hσ1']
    have hden : 0 < (a / L) ^ 2 + (2 * s.im) ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    have e : a / L = a * L / (4 * δ ^ 2) * (4 * (δ ^ 2 / L ^ 2)) := by field_simp
    have hc : 0 ≤ a * L / (4 * δ ^ 2) := by positivity
    calc a / L = a * L / (4 * δ ^ 2) * (4 * (δ ^ 2 / L ^ 2)) := e
      _ ≤ a * L / (4 * δ ^ 2) * ((a / L) ^ 2 + (2 * s.im) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hc
        nlinarith [sq_nonneg (a / L)]
  have hX0 : 0 ≤ Real.log ((q : ℝ) * (|2 * s.im| + 2)) :=
    Real.log_nonneg (by have := two_le_mul_abs_add_two q (2 * s.im); linarith)
  have hX : Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ 2 * L := by
    rw [hLdef]; exact log_mul_abs_two_mul_le q s.im
  have hC3X : C₃ * Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ max C₃ 0 * (2 * L) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hX0).trans (mul_le_mul_of_nonneg_left hX hM₃)
  have hC1L : C₁ * L ≤ max C₁ 0 * L := mul_le_mul_of_nonneg_right (le_max_left _ _) hLpos.le
  have hw : 0 < L / a := div_pos hLpos ha0
  have hKL : K * L ≤ L / a / 4 := by
    calc K * L = K * a * (L / a) := by field_simp
      _ ≤ 1 / 4 * (L / a) := mul_le_mul_of_nonneg_right hKa hw.le
      _ = L / a / 4 := by ring
  have hKL' : K * L = 4 * max C₁ 0 * L + 2 * max C₃ 0 * L + 6 * C₂ * L := by rw [hK]; ring
  have hPw : a * L / (4 * δ ^ 2) ≤ L / a / 16 := by
    calc a * L / (4 * δ ^ 2) = a ^ 2 / (4 * δ ^ 2) * (L / a) := by field_simp
      _ ≤ 1 / 16 * (L / a) := mul_le_mul_of_nonneg_right hδa hw.le
      _ = L / a / 16 := by ring
  have hC2 : 3 * C₂ ≤ 6 * C₂ * L := by
    have h := mul_nonneg hC₂0 (show (0 : ℝ) ≤ 2 * L - 1 by linarith)
    linarith
  linarith [h1, h2, h3, hpb, hC3X, hC1L, hsum, hu, hKL, hKL', hPw, hC2, hP]

end Formalism.ZeroFreeDirichlet
