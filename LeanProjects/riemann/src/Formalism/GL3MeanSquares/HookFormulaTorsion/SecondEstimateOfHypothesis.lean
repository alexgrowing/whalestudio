import Mathlib
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis

open Filter

namespace Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem eventually_le_rpow (a K : ℝ) (ha : 0 < a) : ∀ᶠ x : ℝ in atTop, K ≤ x ^ a :=
  (tendsto_rpow_atTop ha).eventually_ge_atTop K

theorem rpow_eq_rpow_half_mul (x a : ℝ) (hx : 0 < x) : x ^ a = x ^ (a / 2) * x ^ (a / 2) := by
  rw [← Real.rpow_add hx]; congr 1; ring

theorem eventually_mul_log_le_rpow (a K : ℝ) (ha : 0 < a) : ∀ᶠ x : ℝ in atTop, K * Real.log x ≤ x ^ a := by
  have h1 := eventually_le_rpow (a / 2) (|K| * (2 / a)) (by positivity)
  filter_upwards [h1, eventually_ge_atTop 1] with x hx h1x
  have hx0 : 0 < x := by linarith
  have hl : Real.log x ≤ x ^ (a / 2) / (a / 2) := Real.log_le_rpow_div hx0.le (by positivity)
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg h1x
  have hp : 0 < x ^ (a / 2) := Real.rpow_pos_of_pos hx0 _
  calc K * Real.log x ≤ |K| * Real.log x := mul_le_mul_of_nonneg_right (le_abs_self K) hl0
    _ ≤ |K| * (x ^ (a / 2) / (a / 2)) := mul_le_mul_of_nonneg_left hl (abs_nonneg K)
    _ = (|K| * (2 / a)) * x ^ (a / 2) := by field_simp
    _ ≤ x ^ (a / 2) * x ^ (a / 2) := mul_le_mul_of_nonneg_right hx hp.le
    _ = x ^ a := (rpow_eq_rpow_half_mul x a hx0).symm

theorem eventually_log_sq_le_rpow (a K : ℝ) (ha : 0 < a) : ∀ᶠ x : ℝ in atTop, K * Real.log x ^ 2 ≤ x ^ a := by
  filter_upwards [eventually_mul_log_le_rpow (a / 2) |K| (by positivity), eventually_mul_log_le_rpow (a / 2) 1 (by positivity),
    eventually_ge_atTop 1] with x h1 h2 h1x
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg h1x
  have hp : 0 < x ^ (a / 2) := Real.rpow_pos_of_pos hx0 _
  calc K * Real.log x ^ 2 ≤ |K| * Real.log x ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg _)
    _ = (|K| * Real.log x) * (1 * Real.log x) := by ring
    _ ≤ x ^ (a / 2) * x ^ (a / 2) := mul_le_mul h1 h2 (by positivity) hp.le
    _ = x ^ a := (rpow_eq_rpow_half_mul x a hx0).symm

theorem eventually_mul_rpow_log_sq_le_rpow (ε M : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, M * (x ^ (ε / 5) * Real.log x ^ 2) ≤ x ^ ε := by
  filter_upwards [eventually_log_sq_le_rpow (4 * ε / 5) M (by positivity), eventually_ge_atTop 1] with x h h1x
  have hx0 : 0 < x := by linarith
  have hsplit : x ^ ε = x ^ (ε / 5) * x ^ (4 * ε / 5) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hp : 0 < x ^ (ε / 5) := Real.rpow_pos_of_pos hx0 _
  calc M * (x ^ (ε / 5) * Real.log x ^ 2) = x ^ (ε / 5) * (M * Real.log x ^ 2) := by ring
    _ ≤ x ^ (ε / 5) * x ^ (4 * ε / 5) := mul_le_mul_of_nonneg_left h hp.le
    _ = x ^ ε := hsplit.symm

theorem eventually_le_rpow_mul_log_sq (ε K : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, K ≤ x ^ (ε / 5) * Real.log x ^ 2 := by
  filter_upwards [eventually_le_rpow (ε / 5) |K| (by positivity), eventually_ge_atTop (Real.exp 1)] with x h h1x
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) h1x
  have hl : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr h1x
  have hl2 : 1 ≤ Real.log x ^ 2 := one_le_pow₀ hl
  calc K ≤ |K| := le_abs_self K
    _ = |K| * 1 := (mul_one _).symm
    _ ≤ x ^ (ε / 5) * Real.log x ^ 2 := mul_le_mul h hl2 zero_le_one (le_trans (abs_nonneg K) h)

theorem eventually_affine_log_le_rpow (a P Q s : ℝ) (ha : 0 < a) (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, P + Q * Real.log x ≤ s * x ^ a := by
  filter_upwards [eventually_le_rpow a (2 * (P / s)) ha, eventually_mul_log_le_rpow a (2 * (Q / s)) ha] with x h1 h2
  have h3 : P / s + Q / s * Real.log x ≤ x ^ a := by linarith
  calc P + Q * Real.log x = s * (P / s + Q / s * Real.log x) := by field_simp
    _ ≤ s * x ^ a := mul_le_mul_of_nonneg_left h3 hs.le

theorem pow_le_and_rho_le_of_log_bounds (C₀ c Cρ B X h K : ℝ) (hCρ : 0 < Cρ) (hB : 4 ≤ B) (hX : 0 < X) (hh : 0 < h)
    (h1 : C₀ * Real.log B ≤ Real.log X)
    (hK : Cρ * Real.exp (-K) ≤ h / 200)
    (h2 : K * Real.log B ≤ c * Real.log X)
    (h3 : K ≤ c * Real.log X ^ (1 / 2 : ℝ))
    (h4 : 7 * Real.log B - Real.log h ≤ Real.log X / 3) :
    B ^ C₀ ≤ X ∧ rho c Cρ B X ≤ h / 100 ∧ B ^ 7 ≤ h * X ^ (1 / 3 : ℝ) := by
  have hB0 : 0 < B := by linarith
  have hlB : 0 < Real.log B := Real.log_pos (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.rpow_def_of_pos hB0]
    calc Real.exp (Real.log B * C₀) ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr (by linarith)
      _ = X := Real.exp_log hX
  · unfold rho
    have e1 : Real.exp (-c * Real.log X / Real.log B) ≤ Real.exp (-K) := by
      apply Real.exp_le_exp.mpr
      rw [div_le_iff₀ hlB]
      linarith
    have e2 : Real.exp (-c * Real.log X ^ (1 / 2 : ℝ)) ≤ Real.exp (-K) := by
      apply Real.exp_le_exp.mpr
      linarith
    have e3 := mul_le_mul_of_nonneg_left e1 hCρ.le
    have e4 := mul_le_mul_of_nonneg_left e2 hCρ.le
    linarith
  · have p7 : Real.exp (7 * Real.log B) = B ^ 7 := by
      have := Real.exp_nat_mul (Real.log B) 7
      rw [Real.exp_log hB0] at this
      simpa using this
    rw [← p7, Real.rpow_def_of_pos hX]
    calc Real.exp (7 * Real.log B) ≤ Real.exp (Real.log h + Real.log X * (1 / 3)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = h * Real.exp (Real.log X * (1 / 3)) := by rw [Real.exp_add, Real.exp_log hh]

theorem rpow_nine_tenths_le (c₃ B Y : ℝ) (hc₃ : 0 < c₃) (hB : 0 < B) (hY : 0 < Y) (hl : 0 < Real.log Y)
    (h1 : 120 * Real.log B ≤ Real.log Y) (h2 : 40 * Real.log (40 / c₃) ≤ Real.log Y) :
    Y ^ (9 / 10 : ℝ) ≤ c₃ * 1 * B ^ (-6 : ℝ) * Y / Real.log Y := by
  rw [le_div_iff₀ hl, Real.rpow_def_of_pos hY, Real.rpow_def_of_pos hB]
  set l := Real.log Y with hldef
  set b := Real.log B with hbdef
  have hYl : Y = Real.exp l := (Real.exp_log hY).symm
  have a1 : l ≤ 40 * Real.exp (l / 40) := by
    have := Real.add_one_le_exp (l / 40)
    linarith
  have a2 : 40 ≤ c₃ * Real.exp (l / 40) := by
    have : Real.exp (Real.log (40 / c₃)) ≤ Real.exp (l / 40) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_log (by positivity), div_le_iff₀ hc₃] at this
    linarith
  have hE : 0 < Real.exp (l / 40) := Real.exp_pos _
  have hE9 : 0 < Real.exp (l * (9 / 10)) := Real.exp_pos _
  calc Real.exp (l * (9 / 10)) * l ≤ Real.exp (l * (9 / 10)) * (40 * Real.exp (l / 40)) :=
        mul_le_mul_of_nonneg_left a1 hE9.le
    _ ≤ Real.exp (l * (9 / 10)) * ((c₃ * Real.exp (l / 40)) * Real.exp (l / 40)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right a2 hE.le) hE9.le
    _ = c₃ * Real.exp (l * (9 / 10) + l / 40 + l / 40) := by
        rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ c₃ * Real.exp (b * (-6) + l) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hc₃.le
    _ = c₃ * 1 * Real.exp (b * (-6)) * Y := by
        rw [Real.exp_add, ← hYl]; ring

theorem numerical_bound_first : ExponentialRangeSizeConditions := by
  intro ε C C_B C₀ c Cρ c₃ hε hC hCB hC₀ hc hCρ hc₃
  set K : ℝ := Real.log (200 * Cρ) with hKdef
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    ((eventually_mul_rpow_log_sq_le_rpow ε (C₀ * C_B) hε).and ((eventually_mul_rpow_log_sq_le_rpow ε (|K| * C_B / c) hε).and
      ((eventually_le_rpow ε ((K / c) ^ 2) hε).and ((eventually_mul_rpow_log_sq_le_rpow ε (240 * C_B) hε).and
        ((eventually_le_rpow ε (40 * Real.log (40 / c₃)) hε).and (eventually_le_rpow ε 1 hε))))))
  refine ⟨x₀, fun x hx B Y hB hlB hY1 hY2 => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hx₀ x hx
  set β : ℝ := x ^ (ε / 5) * Real.log x ^ 2 with hβ
  set L : ℝ := x ^ ε with hL
  have hlB' : Real.log B ≤ C_B * β := by rw [hβ]; linarith
  have hY0 : 0 < Y := lt_of_lt_of_le (Real.exp_pos _) hY1
  have hl8 : 8 * L ≤ Real.log Y := (Real.le_log_iff_exp_le hY0).mpr hY1
  have hB0 : 0 < B := by linarith
  have hlB0 : 0 < Real.log B := Real.log_pos (by linarith)
  have hlY : 0 < Real.log Y := by linarith
  have k1 : C₀ * Real.log B ≤ Real.log Y := by
    have : C₀ * Real.log B ≤ C₀ * (C_B * β) := mul_le_mul_of_nonneg_left hlB' hC₀.le
    linarith
  have k2 : K * Real.log B ≤ c * Real.log Y := by
    have t1 : K * Real.log B ≤ |K| * Real.log B := mul_le_mul_of_nonneg_right (le_abs_self K) hlB0.le
    have t2 : |K| * Real.log B ≤ |K| * (C_B * β) := mul_le_mul_of_nonneg_left hlB' (abs_nonneg K)
    have t3 : c * (|K| * C_B / c * β) ≤ c * L := mul_le_mul_of_nonneg_left e2 hc.le
    have t4 : c * (|K| * C_B / c * β) = |K| * (C_B * β) := by field_simp
    have t5 : c * L ≤ c * Real.log Y := mul_le_mul_of_nonneg_left (by linarith) hc.le
    linarith
  have k3 : K ≤ c * Real.log Y ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    have t1 : |K / c| ≤ Real.sqrt (Real.log Y) := Real.abs_le_sqrt (by linarith)
    have t2 : K / c ≤ Real.sqrt (Real.log Y) := le_trans (le_abs_self _) t1
    rw [div_le_iff₀ hc] at t2
    linarith
  have hKe : Cρ * Real.exp (-K) ≤ 1 / 200 := by
    rw [Real.exp_neg, hKdef, Real.exp_log (by positivity)]
    apply le_of_eq
    field_simp
  have k4 : 7 * Real.log B - Real.log 1 ≤ Real.log Y / 3 := by
    rw [Real.log_one]; linarith
  obtain ⟨r1, r2, r3⟩ := pow_le_and_rho_le_of_log_bounds C₀ c Cρ B Y 1 K hCρ hB hY0 one_pos k1 hKe k2 k3 k4
  exact ⟨r1, r2, r3, rpow_nine_tenths_le c₃ B Y hc₃ hB0 hY0 hlY (by linarith) (by linarith)⟩

theorem log_four_mul_mul_sq (d N : ℝ) (hd : 0 < d) (hN : 0 < N) :
    Real.log (4 * d * N ^ 2) = Real.log 4 + Real.log d + 2 * Real.log N := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  push_cast; ring

theorem four_le_four_mul_sq (d N : ℝ) (hd : 1 ≤ d) (hN : 1 ≤ N) : 4 ≤ 4 * d * N ^ 2 := by
  have h1 : 1 ≤ N ^ 2 := one_le_pow₀ hN
  have h2 : 1 ≤ d * N ^ 2 := one_le_mul_of_one_le_of_one_le hd h1
  linarith

theorem first_estimate_of_hypothesis : PrimeEstimateOfIntervalHyp := by
  intro C₀ c Cρ c₃ hC₀ hc hCρ hc₃ hInt ε C hε hC
  obtain ⟨x₁, hx₁⟩ := numerical_bound_first ε C 6 C₀ c Cρ c₃ hε hC (by norm_num) hC₀ hc hCρ hc₃
  obtain ⟨x₂, hx₂⟩ := eventually_atTop.mp (eventually_le_rpow_mul_log_sq ε (Real.log 4) hε)
  refine ⟨max x₁ x₂, fun x hx d NE k Y hd hd4 hdX hNE hlNE hk hY1 hY2 => ?_⟩
  have e1 := hx₂ x (le_trans (le_max_right _ _) hx)
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.one_lt.le
  have hN1 : (1 : ℝ) ≤ (NE : ℝ) := by exact_mod_cast hNE
  have hld : Real.log d ≤ x ^ (ε / 5) * Real.log x ^ 2 := by
    have := Real.log_le_log (by linarith) hdX
    rwa [X2, Real.log_exp] at this
  have hlB : Real.log (4 * (d : ℝ) * (NE : ℝ) ^ 2) ≤ 6 * x ^ (ε / 5) * Real.log x ^ 2 := by
    rw [log_four_mul_mul_sq _ _ (by linarith) (by linarith)]
    linarith
  have hYlo : Real.exp (8 * x ^ ε) ≤ Y := by
    have p8 : Real.exp (8 * x ^ ε) = Real.exp (x ^ ε) ^ 8 := by
      have := Real.exp_nat_mul (x ^ ε) 8
      simpa using this
    rw [p8]
    refine le_trans (pow_le_pow_left₀ (Real.exp_pos _).le ?_ 8) hY1
    exact le_mul_of_one_le_left (Real.exp_pos _).le hk
  have hYhi : Y ≤ Real.exp (C * x ^ ε) := by
    rw [mul_comm, Real.exp_mul]; exact hY2
  obtain ⟨r1, r2, r3, r4⟩ := hx₁ x (le_trans (le_max_left _ _) hx) (4 * (d : ℝ) * (NE : ℝ) ^ 2) Y
    (four_le_four_mul_sq _ _ hd1 hN1) hlB hYlo hYhi
  have := hInt d NE Y 1 hd hd4 hNE r1 r2 one_pos le_rfl r3
  have h2 : Y * (1 + 1) = 2 * Y := by ring
  rw [h2] at this
  exact le_trans r4 this

theorem numerical_exclusion_bound : ExclusionInequalities := by
  intro ε A hε hA
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    ((eventually_affine_log_le_rpow ε (Real.log 20) (3 * A) (2 / 5) hε (by norm_num)).and
      ((eventually_le_rpow ε (Real.log 3 * (5 / 4)) hε).and (eventually_ge_atTop (1 : ℝ))))
  refine ⟨x₀, fun x hx r Y hr hY => ?_⟩
  obtain ⟨e1, e2, e3⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  set L : ℝ := x ^ ε with hL
  have hL0 : 0 < L := Real.rpow_pos_of_pos hx0 _
  have hY0 : 0 < Y := lt_of_lt_of_le (Real.exp_pos _) hY
  have hl8 : 8 * L ≤ Real.log Y := (Real.le_log_iff_exp_le hY0).mpr hY
  have hY1 : 1 ≤ Y := by
    refine le_trans ?_ hY
    exact Real.one_le_exp (by positivity)
  set R : ℝ := x ^ A with hR
  have hR1 : 1 ≤ R := Real.one_le_rpow e3 hA.le
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hY34 : 1 ≤ Y ^ (3 / 4 : ℝ) := Real.one_le_rpow hY1 (by norm_num)
  have hY45 : 1 ≤ Y ^ (4 / 5 : ℝ) := Real.one_le_rpow hY1 (by norm_num)
  have s1 : Y ^ (4 / 5 : ℝ) = Y ^ (3 / 4 : ℝ) * Y ^ (1 / 20 : ℝ) := by
    rw [← Real.rpow_add hY0]; norm_num
  have s2 : Y ^ (9 / 10 : ℝ) = Y ^ (4 / 5 : ℝ) * Y ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_add hY0]; norm_num
  have t1 : 20 * R ^ 3 ≤ Y ^ (1 / 20 : ℝ) := by
    have u1 : 20 * R ^ 3 = Real.exp (Real.log 20 + 3 * A * Real.log x) := by
      rw [Real.exp_add, Real.exp_log (by norm_num), hR, Real.rpow_def_of_pos hx0, ← Real.exp_nat_mul]
      congr 2; push_cast; ring
    rw [u1, Real.rpow_def_of_pos hY0]
    exact Real.exp_le_exp.mpr (by linarith)
  have t2 : 3 ≤ Y ^ (1 / 10 : ℝ) := by
    rw [Real.rpow_def_of_pos hY0]
    calc (3 : ℝ) = Real.exp (Real.log 3) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log Y * (1 / 10)) := Real.exp_le_exp.mpr (by linarith)
  constructor
  · have a1 : 3 * (r : ℝ) + 1 ≤ 4 * R := by linarith
    have hr2 : (r : ℝ) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hr0 hr 2
    have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR1
    have a2 : 4 * (r : ℝ) ^ 2 * Y ^ (3 / 4 : ℝ) + 1 ≤ 5 * R ^ 2 * Y ^ (3 / 4 : ℝ) := by
      have v1 : 4 * (r : ℝ) ^ 2 * Y ^ (3 / 4 : ℝ) ≤ 4 * R ^ 2 * Y ^ (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have v2 : 1 ≤ R ^ 2 * Y ^ (3 / 4 : ℝ) := one_le_mul_of_one_le_of_one_le hR2 hY34
      linarith
    calc (3 * (r : ℝ) + 1) * (4 * (r : ℝ) ^ 2 * Y ^ (3 / 4 : ℝ) + 1)
        ≤ (4 * R) * (5 * R ^ 2 * Y ^ (3 / 4 : ℝ)) := mul_le_mul a1 a2 (by positivity) (by positivity)
      _ = Y ^ (3 / 4 : ℝ) * (20 * R ^ 3) := by ring
      _ ≤ Y ^ (3 / 4 : ℝ) * Y ^ (1 / 20 : ℝ) := mul_le_mul_of_nonneg_left t1 (by linarith)
      _ = Y ^ (4 / 5 : ℝ) := s1.symm
  · rw [s2]
    have : Y ^ (4 / 5 : ℝ) * 3 ≤ Y ^ (4 / 5 : ℝ) * Y ^ (1 / 10 : ℝ) :=
      mul_le_mul_of_nonneg_left t2 (by linarith)
    linarith

theorem parameter_choice : ChoiceOfTwoPrimes := by
  intro ε A hε hA
  obtain ⟨x₀, hx₀⟩ := numerical_exclusion_bound ε A hε hA
  refine ⟨x₀, fun x hx r Y GG excl hr hY hGG hexcl => ?_⟩
  obtain ⟨n1, n2⟩ := hx₀ x hx r Y hr hY
  have hY0 : 0 < Y := lt_of_lt_of_le (Real.exp_pos _) hY
  have hpos : (0 : ℝ) < (GG.card : ℝ) := by
    have : 0 < Y ^ (4 / 5 : ℝ) := Real.rpow_pos_of_pos hY0 _
    linarith
  have hne : GG.Nonempty := Finset.card_pos.mp (by exact_mod_cast hpos)
  obtain ⟨g₁, hg₁⟩ := hne
  have hc : (insert g₁ (excl g₁)).card < GG.card := by
    have c1 : (insert g₁ (excl g₁)).card ≤ (excl g₁).card + 1 := Finset.card_insert_le _ _
    have c2 : (((insert g₁ (excl g₁)).card : ℕ) : ℝ) ≤ ((excl g₁).card : ℝ) + 1 := by exact_mod_cast c1
    have c3 := hexcl g₁ hg₁
    have : (((insert g₁ (excl g₁)).card : ℕ) : ℝ) < (GG.card : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨g₂, hg₂, hg₂'⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  rw [Finset.mem_insert, not_or] at hg₂'
  exact ⟨g₁, hg₁, g₂, hg₂, hg₂'.1, hg₂'.2⟩

theorem numerical_estimate_size_conditions : ReciprocalWeightSizeConditions := by
  intro ε δ A integralAdeleSpan C_B C₀ c Cρ hε hδ hA hcT hCB hC₀ hc hCρ
  set K₀ : ℝ := |Real.log (200 * Cρ)| with hK₀
  have hsT : 0 < integralAdeleSpan ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hcT _
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    ((eventually_affine_log_le_rpow δ (C₀ * C_B) 0 integralAdeleSpan hδ hcT).and
      ((eventually_affine_log_le_rpow δ (K₀ * C_B) (A * C_B) (c * integralAdeleSpan) hδ (by positivity)).and
        ((eventually_affine_log_le_rpow (δ / 2) K₀ A (c * integralAdeleSpan ^ (1 / 2 : ℝ)) (by positivity) (by positivity)).and
          ((eventually_affine_log_le_rpow δ (7 * C_B) A (integralAdeleSpan / 3) hδ (by positivity)).and (eventually_ge_atTop (1 : ℝ))))))
  refine ⟨x₀, fun x hx B T m fk hB hlB hm hfk1 hfk2 hT hT0 => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  set L : ℝ := x ^ ε with hL
  set D : ℝ := x ^ δ with hD
  have hL1 : 1 ≤ L := Real.one_le_rpow e5 hε.le
  have hD0 : 0 < D := Real.rpow_pos_of_pos hx0 _
  have hlx : 0 ≤ Real.log x := Real.log_nonneg e5
  have hfk0 : 0 < fk := by linarith
  have hlB0 : 0 < Real.log B := Real.log_pos (by linarith)
  have hlfk : Real.log fk ≤ A * Real.log x := by
    have := Real.log_le_log hfk0 hfk2
    rwa [Real.log_rpow hx0] at this
  have hlfk0 : 0 ≤ Real.log fk := Real.log_nonneg hfk1

  have hT' : integralAdeleSpan * D * L ≤ Real.log T := by
    refine le_trans ?_ hT
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hcT.le) (by linarith)
  set K : ℝ := Real.log (200 * Cρ * fk) with hK
  have hKle : K ≤ K₀ + A * Real.log x := by
    rw [hK, Real.log_mul (by positivity) (by positivity)]
    have := le_abs_self (Real.log (200 * Cρ))
    linarith
  have hK₀0 : 0 ≤ K₀ := abs_nonneg _
  have hK2 : 0 ≤ K₀ + A * Real.log x := by positivity
  have k1 : C₀ * Real.log B ≤ Real.log T := by
    have t1 : C₀ * Real.log B ≤ C₀ * (C_B * L) := mul_le_mul_of_nonneg_left hlB hC₀.le
    have t2 : (C₀ * C_B + 0 * Real.log x) * L ≤ (integralAdeleSpan * D) * L := mul_le_mul_of_nonneg_right e1 (by linarith)
    nlinarith
  have hKe : Cρ * Real.exp (-K) ≤ 1 / fk / 200 := by
    rw [Real.exp_neg, hK, Real.exp_log (by positivity)]
    apply le_of_eq
    field_simp
  have k2 : K * Real.log B ≤ c * Real.log T := by
    have t1 : K * Real.log B ≤ (K₀ + A * Real.log x) * Real.log B := mul_le_mul_of_nonneg_right hKle hlB0.le
    have t2 : (K₀ + A * Real.log x) * Real.log B ≤ (K₀ + A * Real.log x) * (C_B * L) :=
      mul_le_mul_of_nonneg_left hlB hK2
    have t3 : (K₀ * C_B + A * C_B * Real.log x) * L ≤ (c * integralAdeleSpan * D) * L :=
      mul_le_mul_of_nonneg_right e2 (by linarith)
    have t4 : c * (integralAdeleSpan * D * L) ≤ c * Real.log T := mul_le_mul_of_nonneg_left hT' hc.le
    have t5 : (K₀ + A * Real.log x) * (C_B * L) = (K₀ * C_B + A * C_B * Real.log x) * L := by ring
    have t6 : c * (integralAdeleSpan * D * L) = (c * integralAdeleSpan * D) * L := by ring
    linarith
  have k3 : K ≤ c * Real.log T ^ (1 / 2 : ℝ) := by
    have t1 : integralAdeleSpan * D ≤ Real.log T := by
      refine le_trans ?_ hT'
      exact le_mul_of_one_le_right (by positivity) hL1
    have t2 : (integralAdeleSpan * D) ^ (1 / 2 : ℝ) ≤ Real.log T ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) t1 (by norm_num)
    have t3 : (integralAdeleSpan * D) ^ (1 / 2 : ℝ) = integralAdeleSpan ^ (1 / 2 : ℝ) * x ^ (δ / 2) := by
      rw [Real.mul_rpow hcT.le hD0.le, hD, ← Real.rpow_mul hx0.le]
      congr 2; ring
    have t4 : c * (integralAdeleSpan * D) ^ (1 / 2 : ℝ) ≤ c * Real.log T ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left t2 hc.le
    rw [t3] at t4
    linarith
  have k4 : 7 * Real.log B - Real.log (1 / fk) ≤ Real.log T / 3 := by
    rw [one_div, Real.log_inv]
    have t1 : (7 * C_B + A * Real.log x) * L ≤ (integralAdeleSpan / 3 * D) * L := mul_le_mul_of_nonneg_right e4 (by linarith)
    have t2 : A * Real.log x ≤ A * Real.log x * L := le_mul_of_one_le_right (by positivity) hL1
    nlinarith
  exact pow_le_and_rho_le_of_log_bounds C₀ c Cρ B T (1 / fk) K hCρ hB hT0 (by positivity) k1 hKe k2 k3 k4

theorem second_estimate_of_hypothesis : SecondEstimateOfIntervalHypothesis := by
  intro C₀ c Cρ c₃ hC₀ hc hCρ hc₃ hInt ε δ A integralAdeleSpan C_Y hε hδ hA hcT hCY
  obtain ⟨x₁, hx₁⟩ := numerical_estimate_size_conditions ε δ A integralAdeleSpan (8 * C_Y + 1) C₀ c Cρ hε hδ hA hcT (by positivity) hC₀ hc hCρ
  obtain ⟨x₂, hx₂⟩ := eventually_atTop.mp
    ((eventually_le_rpow_mul_log_sq ε (Real.log 4) hε).and ((eventually_mul_rpow_log_sq_le_rpow ε 6 hε).and (eventually_ge_atTop (1 : ℝ))))
  refine ⟨max x₁ x₂, fun x hx d NE g₁ g₂ m fk Ts hd hd4 hdX hNE hlNE hg₁ hg₂ hlg₁ hlg₂ hm hfk1 hfk2 hTs0 hTs => ?_⟩
  obtain ⟨e1, e2, e3⟩ := hx₂ x (le_trans (le_max_right _ _) hx)
  have hx0 : 0 < x := by linarith
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.one_lt.le
  have hN1 : (1 : ℝ) ≤ (NE : ℝ) := by exact_mod_cast hNE
  have hg1 : (1 : ℝ) ≤ (g₁ : ℝ) := by exact_mod_cast hg₁
  have hg2 : (1 : ℝ) ≤ (g₂ : ℝ) := by exact_mod_cast hg₂
  have hNn : 1 ≤ NE * (g₁ * g₂) ^ 2 := Nat.mul_pos hNE (Nat.pow_pos (Nat.mul_pos hg₁ hg₂))
  have hNr : (1 : ℝ) ≤ ((NE * (g₁ * g₂) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hNn
  have hld : Real.log d ≤ x ^ (ε / 5) * Real.log x ^ 2 := by
    have := Real.log_le_log (by linarith) hdX
    rwa [X2, Real.log_exp] at this
  have hlN : Real.log ((NE * (g₁ * g₂) ^ 2 : ℕ) : ℝ) = Real.log NE + 2 * (Real.log g₁ + Real.log g₂) := by
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_mul (by positivity) (by positivity)]
    push_cast; ring
  have hlB : Real.log (4 * (d : ℝ) * ((NE * (g₁ * g₂) ^ 2 : ℕ) : ℝ) ^ 2) ≤ (8 * C_Y + 1) * x ^ ε := by
    rw [log_four_mul_mul_sq _ _ (by linarith) (by linarith), hlN]
    linarith
  have hfk0 : 0 < fk := by linarith
  obtain ⟨r1, r2, r3⟩ := hx₁ x (le_trans (le_max_left _ _) hx) (4 * (d : ℝ) * ((NE * (g₁ * g₂) ^ 2 : ℕ) : ℝ) ^ 2)
    Ts m fk (four_le_four_mul_sq _ _ hd1 hNr) hlB hm hfk1 hfk2 hTs hTs0
  have hh1 : 1 / fk ≤ 1 := by rw [div_le_one hfk0]; exact hfk1
  have hcard := hInt d (NE * (g₁ * g₂) ^ 2) Ts (1 / fk) hd hd4 hNn r1 r2 (by positivity) hh1 r3
  have hm0 : 0 < m := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hm
  have hlTs : 0 < Real.log Ts := lt_of_lt_of_le (by have := Real.rpow_pos_of_pos hx0 ε; positivity) hTs
  have hBpos : 0 < 4 * (d : ℝ) * ((NE * (g₁ * g₂) ^ 2 : ℕ) : ℝ) ^ 2 := by
    have := four_le_four_mul_sq _ _ hd1 hNr
    linarith
  have hpos : 0 < c₃ * (1 / fk) * (4 * (d : ℝ) * ((NE * (g₁ * g₂) ^ 2 : ℕ) : ℝ) ^ 2) ^ (-6 : ℝ) * Ts / Real.log Ts := by
    have := Real.rpow_pos_of_pos hBpos (-6 : ℝ)
    positivity
  have hcpos : (0 : ℝ) < ((normPrimes d (NE * (g₁ * g₂) ^ 2) Ts (Ts * (1 + 1 / fk))).card : ℝ) :=
    lt_of_lt_of_le hpos hcard
  obtain ⟨T, hT⟩ := Finset.card_pos.mp (by exact_mod_cast hcpos :
    0 < (normPrimes d (NE * (g₁ * g₂) ^ 2) Ts (Ts * (1 + 1 / fk))).card)
  simp only [normPrimes, Finset.mem_filter, Finset.mem_Icc] at hT
  obtain ⟨⟨_, hTle⟩, hTp, hTlo, hTn⟩ := hT
  refine ⟨T, hTp, hTlo.le, ?_, hTn⟩
  have hhi : 0 ≤ Ts * (1 + 1 / fk) := by positivity
  exact le_trans (by exact_mod_cast hTle) (Nat.floor_le hhi)

theorem exceptional_set_size : TstarSize := by
  intro ε δ A C hε hδ hA hC
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    ((eventually_le_rpow (2 * ε / 3) 8 (by positivity)).and
      ((eventually_affine_log_le_rpow ε 0 A (1 / 8) hε (by norm_num)).and
        ((eventually_le_rpow δ (8 * C) hδ).and ((eventually_le_rpow δ 8 hδ).and (eventually_ge_atTop (1 : ℝ))))))
  refine ⟨x₀, fun x hx m k n hn1 hn2 hm hk => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have hn0 : 0 < n := by linarith
  set L : ℝ := x ^ ε with hL
  set s : ℝ := x ^ (ε / 3) with hs
  have hL1 : 1 ≤ L := Real.one_le_rpow e5 hε.le
  have hs0 : 0 < s := Real.rpow_pos_of_pos hx0 _
  have hLs : L = s * x ^ (2 * ε / 3) := by
    rw [hL, hs, ← Real.rpow_add hx0]; congr 1; ring
  have hs8 : 8 * s ≤ L := by
    rw [hLs]
    have := mul_le_mul_of_nonneg_left e1 hs0.le
    linarith
  have hm8C : 8 * C ≤ m := le_trans e3 hm
  have hm8 : 8 ≤ m := le_trans e4 hm
  have hm0 : 0 < m := by linarith
  have hln : Real.log n ≤ A * Real.log x := by
    have := Real.log_le_log hn0 hn2
    rwa [Real.log_rpow hx0] at this
  have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hk
  have hq : m ^ 2 * L / k ≤ 1 := by rw [div_le_one hk0]; exact hk
  have hlog : Real.log (x * Real.exp L / Real.exp s / (x * n)) = L - s - Real.log n := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp, Real.log_exp]
    ring
  have hmL : 8 ≤ m * L := by
    have := mul_le_mul hm8 hL1 zero_le_one hm0.le
    linarith
  constructor
  · rw [hlog]
    have t1 : 3 * L / 4 ≤ L - s - Real.log n := by linarith
    have t2 : m * (3 * L / 4) ≤ m * (L - s - Real.log n) := mul_le_mul_of_nonneg_left t1 hm0.le
    have t3 : C * (L + m ^ 2 * L / k) ≤ C * (2 * L) := mul_le_mul_of_nonneg_left (by linarith) hC.le
    have t4 : 8 * C * L ≤ m * L := mul_le_mul_of_nonneg_right hm8C (by linarith)
    linarith
  · intro Xu Gam fk hXu hGam hfk hlX hlG
    have hG0 : 0 < Gam := by linarith
    rw [Real.log_mul hXu.ne' (Real.rpow_pos_of_pos hG0 _).ne', Real.log_rpow hG0]
    have t1 : Real.log Gam / fk ≤ 1 := by rw [div_le_one hfk]; exact hlG
    have t2 : -2 / fk * Real.log Gam = -2 * (Real.log Gam / fk) := by ring
    rw [t2]
    linarith

end Formalism.HermitianLattices.ZeroFreeRegionGL2
