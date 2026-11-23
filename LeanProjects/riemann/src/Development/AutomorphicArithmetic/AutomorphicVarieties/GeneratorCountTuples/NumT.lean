import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.Bridge

open NumberField UpperTheory.V UpperTheory.V.K

theorem UpperTheory.V.K.numT :
    ∀ C : ℝ, ∃ C' : ℝ, ∀ e n D : ℕ, 1 ≤ e → 1 ≤ n → 1 ≤ D → tBound C (2 * e) (4 * e + 4) n D ≤ kBound C' e n D := by
  intro C
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2304 * |C|) (one_lt_two : (1 : ℝ) < 2)
  refine ⟨((k + 6 : ℕ) : ℝ), fun e n D he hn hD => ?_⟩
  unfold tBound kBound
  rw [Real.rpow_natCast, Real.exp_le_exp]
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hm : ((2 * e : ℕ) : ℝ) = 2 * e := by push_cast; ring
  have hN : ((4 * e + 4 : ℕ) : ℝ) = 4 * e + 4 := by push_cast; ring
  rw [hm, hN]
  set y : ℝ := 2 * (e : ℝ) * n with hy
  set N : ℝ := 4 * (e : ℝ) + 4 with hNdef
  set L : ℝ := Real.log (2 * (D : ℝ)) with hL
  have hen : (e : ℝ) ≤ e * n := by nlinarith
  have hne : (n : ℝ) ≤ e * n := by nlinarith
  have hy2 : 2 ≤ y := by rw [hy]; nlinarith
  have hmy : 2 * (e : ℝ) ≤ y := by rw [hy]; nlinarith
  have hNy : N ≤ 4 * y := by rw [hNdef]; linarith
  have hN1 : 1 ≤ N := by rw [hNdef]; linarith
  have hdy : (n : ℝ) * N ≤ 4 * y := by rw [hNdef, hy]; nlinarith
  have hd1 : 1 ≤ (n : ℝ) * N := by nlinarith
  have hL2 : 1 / 2 ≤ L := by
    have h1 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    have := Real.log_two_gt_d9
    linarith
  have hlogd : Real.log ((n : ℝ) * N) ≤ 4 * y :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hlogd0 : 0 ≤ Real.log ((n : ℝ) * N) := Real.log_nonneg hd1
  have hsplit : Real.log (2 * (D : ℝ) * ((n : ℝ) * N)) = L + Real.log ((n : ℝ) * N) :=
    Real.log_mul (by positivity) (by positivity)
  set G : ℝ := Real.log (2 * (D : ℝ) * ((n : ℝ) * N)) with hG
  have hG0 : 0 ≤ G := by rw [hsplit]; linarith
  have hGle : G ≤ 9 * y * L := by rw [hsplit]; nlinarith
  have hy0 : 0 ≤ y := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hd0 : 0 ≤ (n : ℝ) * N := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hA0 : 0 ≤ 2 * (e : ℝ) * ((n : ℝ) * N) ^ 3 * N * G := by positivity
  have hA : 2 * (e : ℝ) * ((n : ℝ) * N) ^ 3 * N * G ≤ y * (4 * y) ^ 3 * (4 * y) * (9 * y * L) := by
    gcongr
  have hk' : 2304 * |C| ≤ y ^ k := hk.le.trans (pow_le_pow_left₀ (by norm_num) hy2 k)
  calc C * (2 * (e : ℝ)) * ((n : ℝ) * N) ^ 3 * N * G
      = C * (2 * (e : ℝ) * ((n : ℝ) * N) ^ 3 * N * G) := by ring
    _ ≤ |C| * (2 * (e : ℝ) * ((n : ℝ) * N) ^ 3 * N * G) := mul_le_mul_of_nonneg_right (le_abs_self C) hA0
    _ ≤ |C| * (y * (4 * y) ^ 3 * (4 * y) * (9 * y * L)) := mul_le_mul_of_nonneg_left hA (abs_nonneg C)
    _ = (2304 * |C|) * (y ^ 6 * L) := by ring
    _ ≤ y ^ k * (y ^ 6 * L) := mul_le_mul_of_nonneg_right hk' (by positivity)
    _ = y ^ (k + 6) * L := by ring
