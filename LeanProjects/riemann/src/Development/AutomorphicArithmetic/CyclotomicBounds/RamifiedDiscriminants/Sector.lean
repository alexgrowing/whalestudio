import Mathlib

open Complex

namespace UpperTheory.Ram.Sector

noncomputable def sec (w : ℕ) (z : ℂ) : ℕ := ⌊(w : ℝ) * arg z / (2 * Real.pi)⌋₊

theorem measurable_sec (w : ℕ) : Measurable (sec w) := by
  unfold sec
  exact Nat.measurable_floor.comp ((measurable_const.mul measurable_arg).div_const _)

theorem sec_lt {w : ℕ} (hw : 0 < w) (z : ℂ) : sec w z < w := by
  unfold sec
  have hp := Real.pi_pos
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  rw [Nat.floor_lt' hw.ne', div_lt_iff₀ (by positivity)]
  have := arg_le_pi z
  nlinarith

theorem eq_one_of_sec_eq {w : ℕ} (hw : 0 < w) {ζ z : ℂ} (hζ : ζ ^ w = 1) (hz : 0 < z.im) (hz' : 0 < (ζ * z).im)
    (h : sec w z = sec w (ζ * z)) : ζ = 1 := by
  have hp := Real.pi_pos
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hz0 : z ≠ 0 := fun e => by simp [e] at hz
  have hn : ‖ζ‖ = 1 := by
    have := congrArg norm hζ
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hw.ne').1 this
  have a0 : 0 ≤ arg z := arg_nonneg_iff.2 hz.le
  have b0 : 0 ≤ arg (ζ * z) := arg_nonneg_iff.2 hz'.le
  set a := arg z with ha
  set b := arg (ζ * z) with hb
  have hζe : ζ = exp (((b - a : ℝ) : ℂ) * I) := by
    have e1 := norm_mul_exp_arg_mul_I z
    have e2 := norm_mul_exp_arg_mul_I (ζ * z)
    rw [norm_mul, hn, one_mul] at e2
    have hz1 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz0
    have e3 : exp ((b : ℂ) * I) = ζ * exp ((a : ℂ) * I) := by
      apply mul_left_cancel₀ hz1
      rw [e2]
      conv_lhs => rw [← e1]
      ring
    push_cast
    rw [sub_mul, exp_sub, e3, mul_div_assoc, div_self (exp_ne_zero _), mul_one]
  rw [hζe, ← exp_nat_mul, exp_eq_one_iff] at hζ
  obtain ⟨n, hn'⟩ := hζ
  have hn2 : (w : ℝ) * (b - a) = n * (2 * Real.pi) := by
    have : (((w : ℝ) * (b - a) : ℝ) : ℂ) * I = ((n * (2 * Real.pi) : ℝ) : ℂ) * I := by
      push_cast at hn' ⊢
      linear_combination hn'
    exact_mod_cast mul_right_cancel₀ I_ne_zero this
  unfold sec at h
  rw [← ha, ← hb] at h
  have x0 : 0 ≤ (w : ℝ) * a / (2 * Real.pi) := by positivity
  have y0 : 0 ≤ (w : ℝ) * b / (2 * Real.pi) := by positivity
  have l1 := Nat.floor_le x0
  have l2 := Nat.lt_floor_add_one ((w : ℝ) * a / (2 * Real.pi))
  have l3 := Nat.floor_le y0
  have l4 := Nat.lt_floor_add_one ((w : ℝ) * b / (2 * Real.pi))
  rw [h] at l1 l2
  have hd : (w : ℝ) * b / (2 * Real.pi) - (w : ℝ) * a / (2 * Real.pi) = n := by
    field_simp
    linarith
  have n1 : (n : ℝ) < 1 := by linarith
  have n2 : (-1 : ℝ) < n := by linarith
  have n0 : n = 0 := by
    have : n < 1 := by exact_mod_cast n1
    have : -1 < n := by exact_mod_cast n2
    omega
  rw [n0] at hn2
  have : b - a = 0 := by
    have h5 : (w : ℝ) * (b - a) = 0 := by simpa using hn2
    exact (mul_eq_zero.1 h5).resolve_left hw'.ne'
  rw [hζe, this]
  simp

theorem pow_torsionOrder {E : Type} [Field E] [NumberField E] {x : E} (h : ∃ n : ℕ, 0 < n ∧ x ^ n = 1) :
    x ^ NumberField.Units.torsionOrder E = 1 := by
  obtain ⟨n, hn, hx⟩ := h
  have hi : IsIntegral ℤ x := IsIntegral.of_pow hn (hx ▸ isIntegral_one)
  let y : NumberField.RingOfIntegers E := ⟨x, hi⟩
  have hy : y ^ n = 1 := by
    apply NumberField.RingOfIntegers.ext
    rw [show ((y ^ n : NumberField.RingOfIntegers E) : E) = x ^ n from map_pow (algebraMap _ E) y n, hx]
    rfl
  let u : (NumberField.RingOfIntegers E)ˣ := Units.ofPowEqOne y n hy hn.ne'
  have hu : u ∈ NumberField.Units.torsion E := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨n, hn, Units.ext (by simpa [u] using hy)⟩
  have h1 : (⟨u, hu⟩ : NumberField.Units.torsion E) ^ NumberField.Units.torsionOrder E = 1 := by
    unfold NumberField.Units.torsionOrder
    first | exact pow_card_eq_one' | exact pow_card_eq_one
  have h2 : u ^ NumberField.Units.torsionOrder E = 1 := by simpa using congrArg Subtype.val h1
  have h3 : y ^ NumberField.Units.torsionOrder E = 1 := by simpa [u] using congrArg Units.val h2
  have h4 := congrArg (algebraMap (NumberField.RingOfIntegers E) E) h3
  rw [map_pow, map_one] at h4
  exact h4

open MeasureTheory in

theorem sum_le_of_layers {X J : Type*} [MeasurableSpace X] (μ : Measure X) (T : J → Set X) (s : X → ℕ) (w : ℕ)
    (hw : ∀ x, s x < w) (J0 : Finset J) (M : ENNReal)
    (h : ∀ k, ∑ j ∈ J0, μ (T j ∩ {x | s x = k}) ≤ M) : ∑ j ∈ J0, μ (T j) ≤ w * M := by
  have h1 : ∀ j, μ (T j) ≤ ∑ k ∈ Finset.range w, μ (T j ∩ {x | s x = k}) := fun j => by
    refine le_trans (measure_mono ?_) (measure_biUnion_finset_le _ _)
    intro x hx
    exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 (hw x))) ⟨hx, rfl⟩
  calc ∑ j ∈ J0, μ (T j) ≤ ∑ j ∈ J0, ∑ k ∈ Finset.range w, μ (T j ∩ {x | s x = k}) := Finset.sum_le_sum fun j _ => h1 j
    _ = ∑ k ∈ Finset.range w, ∑ j ∈ J0, μ (T j ∩ {x | s x = k}) := Finset.sum_comm
    _ ≤ ∑ _k ∈ Finset.range w, M := Finset.sum_le_sum fun k _ => h k
    _ = w * M := by simp

theorem eight_sq_le {f r : ℕ} (hf : 1 ≤ f) (hr : 2 ≤ r) : 8 * f ^ 2 ≤ 2 ^ (f * r ^ 2) := by
  have h1 : f ≤ 2 ^ (f - 1) := by
    have := Nat.lt_two_pow_self (n := f - 1)
    omega
  have h2 : 4 ≤ r ^ 2 := by nlinarith
  calc 8 * f ^ 2 ≤ 2 ^ 3 * (2 ^ (f - 1)) ^ 2 := by gcongr; norm_num
    _ = 2 ^ (3 + (f - 1) * 2) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (f * r ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith [Nat.sub_add_cancel hf])

theorem le_of_mul_le {w N : ℕ} (hw : w ≤ 2 ^ N) {a M : ENNReal}
    (h : ENNReal.ofReal ((1 / 16 : ℝ) ^ N) * a ≤ w * M) : ENNReal.ofReal ((1 / 32 : ℝ) ^ N) * a ≤ M := by
  have e : ENNReal.ofReal ((1 / 16 : ℝ) ^ N) = (2 ^ N : ℕ) * ENNReal.ofReal ((1 / 32 : ℝ) ^ N) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    push_cast
    rw [← mul_pow]
    norm_num
  have h2 : ((2 ^ N : ℕ) : ENNReal) * (ENNReal.ofReal ((1 / 32 : ℝ) ^ N) * a) ≤ ((2 ^ N : ℕ) : ENNReal) * M := by
    rw [← mul_assoc, ← e]
    exact h.trans (by gcongr)
  exact (ENNReal.mul_le_mul_iff_right (by simp) (ENNReal.natCast_ne_top _)).1 h2

end UpperTheory.Ram.Sector
