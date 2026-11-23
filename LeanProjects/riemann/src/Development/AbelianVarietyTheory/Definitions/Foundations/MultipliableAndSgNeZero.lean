import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CthFac

noncomputable section

open scoped UpperHalfPlane

namespace GlobalTheory.Sieg.Model

theorem admissible_example_alt : admitted 5 ![1 / 3, 0] := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rintro ⟨⟨n, hn⟩, -⟩
  simp at hn
  have h : (3 * n : ℤ) = 5 := by
    have : (3 * (n : ℚ)) = 5 := by rw [hn]; norm_num
    exact_mod_cast this
  omega

theorem exponent_exact {c : ℕ} (h : Nat.Coprime c 6) :
    12 * ((c ^ 2 - 1) / 12) + 1 = c ^ 2 ∧ 2 * (((c : ℤ) - (c : ℤ) ^ 2) / 2) = (c : ℤ) - (c : ℤ) ^ 2 := by
  constructor
  · have h2 : ¬ 2 ∣ c := fun hh => by
      have := Nat.dvd_gcd hh (show 2 ∣ 6 by norm_num); rw [h] at this; omega
    have h3 : ¬ 3 ∣ c := fun hh => by
      have := Nat.dvd_gcd hh (show 3 ∣ 6 by norm_num); rw [h] at this; omega
    have h12 : c ^ 2 % 12 = 1 := by
      rw [Nat.pow_mod]
      have : c % 12 = 1 ∨ c % 12 = 5 ∨ c % 12 = 7 ∨ c % 12 = 11 := by omega
      rcases this with h | h | h | h <;> rw [h]
    omega
  · apply Int.mul_ediv_cancel'
    have : (c : ℤ) - (c : ℤ) ^ 2 = -((c : ℤ) * (c - 1)) := by ring
    rw [this]
    exact (dvd_neg).2 (Int.even_mul_pred_self (c : ℤ)).two_dvd

theorem ee_ne_zero (z : ℂ) : ee z ≠ 0 := Complex.exp_ne_zero _

theorem ee_add (z w : ℂ) : ee (z + w) = ee z * ee w := by
  simp only [ee, mul_add, Complex.exp_add]

theorem ee_nat_mul (n : ℕ) (z : ℂ) : ee (n * z) = ee z ^ n := by
  simp only [ee, ← Complex.exp_nat_mul]; congr 1; ring

theorem ee_neg (z : ℂ) : ee (-z) = (ee z)⁻¹ := by
  simp only [ee, ← Complex.exp_neg]; congr 1; ring

theorem norm_ee (z : ℂ) : ‖ee z‖ = Real.exp (-(2 * Real.pi * z.im)) := by
  simp [ee, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem norm_ee_lt_one (τ : ℍ) : ‖ee τ‖ < 1 := by
  rw [norm_ee, Real.exp_lt_one_iff]
  have := τ.im_pos
  have h : 0 < 2 * Real.pi * (τ : ℂ).im := by
    have := Real.pi_pos
    simp only [UpperHalfPlane.coe_im]; positivity
  linarith

theorem ee_eq_one {a b : ℚ} (τ : ℍ) (h : ee ((a : ℂ) * τ + b) = 1) : a = 0 ∧ ∃ n : ℤ, (n : ℚ) = b := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  have hp : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have h1 : (a : ℂ) * τ + b = n := by
    apply mul_left_cancel₀ hp; rw [hn]; ring
  have him := congrArg Complex.im h1
  simp at him
  have ha : a = 0 := by
    rcases him with h | h
    · exact h
    · exact absurd h τ.im_pos.ne'
  refine ⟨ha, n, ?_⟩
  subst ha
  simp at h1
  exact_mod_cast h1.symm

theorem ne_one_of_not_int {y : Fin 2 → ℚ}
    (hy : ¬ (y 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ y 1 ∈ Set.range ((↑) : ℤ → ℚ))) (τ : ℍ) (m : ℕ) :
    1 - ee τ ^ m * ee (pt y τ) ≠ 0 ∧ 1 - ee τ ^ m * (ee (pt y τ))⁻¹ ≠ 0 := by
  constructor
  · intro h
    have h' : ee ((((m : ℚ) + y 0 : ℚ) : ℂ) * τ + (y 1 : ℚ)) = 1 := by
      rw [sub_eq_zero, ← ee_nat_mul, ← ee_add] at h
      rw [h]; congr 1; simp [pt]; ring
    obtain ⟨h0, n, hn⟩ := ee_eq_one τ h'
    exact hy ⟨⟨-m, by push_cast; linarith⟩, ⟨n, hn⟩⟩
  · intro h
    have h' : ee ((((m : ℚ) - y 0 : ℚ) : ℂ) * τ + (-y 1 : ℚ)) = 1 := by
      rw [sub_eq_zero, ← ee_nat_mul, ← ee_neg, ← ee_add] at h
      rw [h]; congr 1; simp [pt]; ring
    obtain ⟨h0, n, hn⟩ := ee_eq_one τ h'
    exact hy ⟨⟨m, by push_cast; linarith⟩, ⟨-n, by push_cast; linarith⟩⟩

theorem hasProd_geom {q : ℂ} (hq : ‖q‖ < 1) (a : ℂ) (h : ∀ m : ℕ, 1 - q ^ (m + 1) * a ≠ 0) :
    ∃ P : ℂ, P ≠ 0 ∧ HasProd (fun m : ℕ => 1 - q ^ (m + 1) * a) P := by
  have hs : Summable fun m : ℕ => ‖-(q ^ (m + 1) * a)‖ := by
    simp only [norm_neg, norm_mul, norm_pow, pow_succ]
    exact ((summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right _).mul_right _
  refine ⟨∏' m : ℕ, (1 + -(q ^ (m + 1) * a)), ?_, ?_⟩
  · exact tprod_one_add_ne_zero_of_summable (fun m => by simpa [sub_eq_add_neg] using h m) hs
  · simpa [sub_eq_add_neg] using (multipliable_one_add_of_summable hs).hasProd

theorem hasProd_inv {f : ℕ → ℂ} {P : ℂ} (h : HasProd f P) (hP : P ≠ 0) : HasProd (fun m => (f m)⁻¹) P⁻¹ := by
  have := Filter.Tendsto.inv₀ h hP
  simpa [HasProd, Finset.prod_inv_distrib] using this

theorem hasProd_pow {f : ℕ → ℂ} {P : ℂ} (h : HasProd f P) (k : ℕ) : HasProd (fun m => (f m) ^ k) (P ^ k) := by
  have := Filter.Tendsto.pow h k
  simpa [HasProd, Finset.prod_pow] using this

theorem ee_pt_pow (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : ee (pt x τ) ^ c = ee (pt (c • x) τ) := by
  rw [← ee_nat_mul]; congr 1; simp [pt]; ring

theorem multipliable_and_sg_ne_zero {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) (τ : ℍ) :
    Multipliable (fun m : ℕ => cthFac c (ee τ) (ee (pt x τ)) (m + 1)) ∧ 1 - ee (pt x τ) ^ c ≠ 0 ∧ sg c x τ ≠ 0 := by
  have hc : ¬ ((c • x) 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ (c • x) 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
    simpa using h.2.2
  have hx : ¬ (x 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ x 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact h.2.2 ⟨⟨c * a, by rw [← ha]; push_cast; ring⟩, ⟨c * b, by rw [← hb]; push_cast; ring⟩⟩
  have hq := norm_ee_lt_one τ
  obtain ⟨A, hA, pA⟩ := hasProd_geom hq _ fun m => (ne_one_of_not_int hx τ (m + 1)).1
  obtain ⟨B, hB, pB⟩ := hasProd_geom hq _ fun m => (ne_one_of_not_int hx τ (m + 1)).2
  obtain ⟨C, hC, pC⟩ := hasProd_geom hq _ fun m => (ne_one_of_not_int hc τ (m + 1)).1
  obtain ⟨D, hD, pD⟩ := hasProd_geom hq _ fun m => (ne_one_of_not_int hc τ (m + 1)).2
  have hP : HasProd (fun m : ℕ => cthFac c (ee τ) (ee (pt x τ)) (m + 1)) (A ^ (c ^ 2) * B ^ (c ^ 2) * (C * D)⁻¹) := by
    have := ((hasProd_pow pA (c ^ 2)).mul (hasProd_pow pB (c ^ 2))).mul (hasProd_inv (pC.mul pD) (mul_ne_zero hC hD))
    simpa only [cthFac, ee_pt_pow, div_eq_mul_inv] using this
  have h1 : 1 - ee (pt x τ) ^ c ≠ 0 := by
    have := (ne_one_of_not_int hc τ 0).1
    rwa [pow_zero, one_mul, ← ee_pt_pow] at this
  have h2 : 1 - ee (pt x τ) ≠ 0 := by
    have := (ne_one_of_not_int hx τ 0).1
    rwa [pow_zero, one_mul] at this
  refine ⟨hP.multipliable, h1, ?_⟩
  unfold sg cth
  rw [hP.tprod_eq]
  have e1 := ee_ne_zero (τ : ℂ)
  have e2 : -ee (pt x τ) ≠ 0 := neg_ne_zero.2 (ee_ne_zero _)
  refine mul_ne_zero (div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ e1) (zpow_ne_zero _ e2)) (pow_ne_zero _ h2)) h1) ?_
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ hB)) (inv_ne_zero (mul_ne_zero hC hD))

theorem sg_translate (c : ℕ) (x : Fin 2 → ℚ) (τ τ' : ℍ) (h : (τ' : ℂ) = τ + 1) :
    sg c x τ' = sg c ![x 0, x 0 + x 1] τ := by
  have e1 : ee 1 = 1 := by simp [ee]
  unfold sg
  congr 1
  · rw [h, ee_add, e1, mul_one]
  · congr 1; simp [pt, h]; ring

theorem f_zero_two_eq (b : ℚ) : f0 2 ![0, b] = -1 / 12 := by
  simp [f0, Polynomial.bernoulli_eval_zero, bernoulli_eq_bernoulli'_of_ne_one]
  norm_num

theorem f_zero_one_third (b : ℚ) : f0 1 ![4 / 3, b] = 1 / 6 := by
  have : Int.fract (4 / 3 : ℚ) = 1 / 3 := by
    rw [Int.fract_eq_iff]; exact ⟨by norm_num, by norm_num, 1, by norm_num⟩
  simp [f0, this]
  norm_num

theorem summable_exp_abs {a : ℝ} (ha : 0 < a) : Summable fun n : ℤ => Real.exp (-(a * |(n : ℝ)|)) := by
  have hs : Summable fun n : ℕ => Real.exp (-(a * n)) := by
    have := summable_geometric_of_lt_one (Real.exp_pos (-a)).le (Real.exp_lt_one_iff.2 (by linarith))
    refine this.congr fun n => ?_
    rw [← Real.exp_nat_mul]; congr 1; ring
  apply Summable.of_nat_of_neg <;> simpa using hs

theorem summable_pow_exp_abs {a : ℝ} (ha : 0 < a) (k : ℕ) (s : ℝ) :
    Summable fun n : ℤ => |s + n| ^ k * Real.exp (-(2 * a * |s + n|)) := by
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
    ((summable_exp_abs ha).mul_left ((k.factorial : ℝ) / a ^ k * Real.exp (a * |s|)))
  have h1 := Real.pow_div_factorial_le_exp (a * |s + n|) (by positivity) k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h2 : |s + n| ^ k ≤ (k.factorial : ℝ) / a ^ k * Real.exp (a * |s + n|) := by
    rw [div_le_iff₀ hk, mul_pow] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  have h3 : |(n : ℝ)| ≤ |s + n| + |s| := by
    have := abs_sub (s + n) s
    simpa using this
  calc |s + n| ^ k * Real.exp (-(2 * a * |s + n|))
      ≤ ((k.factorial : ℝ) / a ^ k * Real.exp (a * |s + n|)) * Real.exp (-(2 * a * |s + n|)) := by gcongr
    _ = (k.factorial : ℝ) / a ^ k * Real.exp (-(a * |s + n|)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ (k.factorial : ℝ) / a ^ k * Real.exp (a * |s| + -(a * |(n : ℝ)|)) := by
        gcongr; nlinarith
    _ = _ := by rw [Real.exp_add, mul_assoc]

theorem summable_fTerm (j : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : Summable (fTerm j x τ) := by
  have hy : 0 < τ.im := τ.im_pos
  have hπ := Real.pi_pos
  have hN : (0 : ℝ) < (x 0).den := by exact_mod_cast (x 0).den_pos
  have s1 := summable_pow_exp_abs (a := Real.pi * τ.im / 2) (by positivity) (j - 1) (x 0 : ℝ)
  have s2 := summable_exp_abs (a := Real.pi * τ.im / (x 0).den) (by positivity)
  refine Summable.of_norm_bounded (s1.mul_of_nonneg s2 (fun _ => by positivity) (fun _ => by positivity)) ?_
  rintro ⟨n, d⟩
  unfold fTerm
  split_ifs with h
  · have hν : x 0 + n ≠ 0 := fun h0 => by simp [h0] at h
    have hd : d ≠ 0 := fun h0 => by simp [h0] at h
    have hd1 : (1 : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast Int.one_le_abs hd
    have hint : ((x 0).den : ℚ) * (x 0 + n) = (((x 0).num + (x 0).den * n : ℤ) : ℚ) := by
      push_cast; rw [mul_add, Rat.den_mul_eq_num]
    have hk0 : ((x 0).num + (x 0).den * n : ℤ) ≠ 0 := fun h0 => by
      rw [h0] at hint
      exact hν (by simpa using hint)
    have hν1 : (1 : ℝ) ≤ (x 0).den * |(x 0 : ℝ) + n| := by
      have h1 : (1 : ℝ) ≤ |((((x 0).num + (x 0).den * n : ℤ) : ℚ) : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
      rw [← hint] at h1
      push_cast at h1
      rwa [abs_mul, abs_of_pos hN] at h1
    have hpos : (0 : ℝ) < ((x 0 : ℝ) + n) * d := by exact_mod_cast h
    have habs : ((x 0 : ℝ) + n) * d = |(x 0 : ℝ) + n| * |(d : ℝ)| := by rw [← abs_mul, abs_of_pos hpos]
    have hs : ‖(Int.sign d : ℂ)‖ = 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast Int.abs_sign_of_ne_zero hd
    have hn : ‖((x 0 + n : ℚ) : ℂ)‖ = |(x 0 : ℝ) + n| := by
      rw [Complex.norm_ratCast]; push_cast; rfl
    simp only [norm_mul, norm_pow, hs, hn, norm_ee, one_mul]
    have i1 : (((x 0 + n : ℚ) : ℂ) * d * (τ : ℂ)).im = ((x 0 : ℝ) + n) * d * τ.im := by
      simp [Complex.mul_im]
    have i2 : ((x 1 : ℂ) * d).im = 0 := by simp [Complex.mul_im]
    rw [i1, i2, habs, mul_zero, neg_zero, Real.exp_zero, mul_one,
      mul_assoc (|(x 0 : ℝ) + n| ^ (j - 1)), ← Real.exp_add]
    gcongr
    set u := |(x 0 : ℝ) + n|
    set v := |(d : ℝ)|
    have hu : 0 ≤ u := abs_nonneg _
    have a1 : u ≤ u * v := by nlinarith
    have a2 : v / (x 0).den ≤ u * v := by
      rw [div_le_iff₀ hN]; nlinarith
    have hp : 0 < Real.pi * τ.im := by positivity
    have e : Real.pi * τ.im / (x 0).den * v = Real.pi * τ.im * (v / (x 0).den) := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left a1 hp.le, mul_le_mul_of_nonneg_left a2 hp.le]
  · simp only [norm_zero]; positivity

end GlobalTheory.Sieg.Model
