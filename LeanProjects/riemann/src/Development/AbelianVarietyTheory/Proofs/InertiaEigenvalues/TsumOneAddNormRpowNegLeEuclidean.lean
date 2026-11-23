import Mathlib

open MeasureTheory Metric Module
open scoped ENNReal

namespace GlobalTheory.LatticeCount

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

lemma one_add_norm_rpow_neg_le {s r : ℝ} (hs : 0 ≤ s) {x y : V} (hx : r ≤ ‖x‖)
    (hy : y ∈ ball x (r / 2)) :
    (1 + ‖x‖) ^ (-s) ≤ 2 ^ s * (1 + ‖y‖) ^ (-s) := by
  have hd : dist y x < r / 2 := mem_ball.mp hy
  rw [dist_eq_norm] at hd
  have h1 := norm_sub_norm_le y x
  have hx0 := norm_nonneg x
  have key : 1 + ‖y‖ ≤ 2 * (1 + ‖x‖) := by linarith
  have hpos : 0 < 1 + ‖y‖ := by positivity
  calc (1 + ‖x‖) ^ (-s) = 2 ^ s * (2 * (1 + ‖x‖)) ^ (-s) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← mul_assoc, ← Real.rpow_add (by norm_num)]
        simp
    _ ≤ 2 ^ s * (1 + ‖y‖) ^ (-s) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hpos key (by linarith)) (by positivity)

lemma sum_mul_measure_ball_le [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] {s : ℝ} (hs : 0 ≤ s) (Λ : AddSubgroup V) {r : ℝ} (hr : 0 < r)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → r ≤ ‖x‖) (t : Finset ((Λ : Set V) \ {0} : Set V)) :
    (∑ x ∈ t, ENNReal.ofReal ((1 + ‖(x : V)‖) ^ (-s))) * μ (ball 0 (r / 2)) ≤
      ENNReal.ofReal (2 ^ s) * ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ := by
  classical
  have hpt : ∀ x ∈ t, ENNReal.ofReal ((1 + ‖(x : V)‖) ^ (-s)) * μ (ball 0 (r / 2)) ≤
      ENNReal.ofReal (2 ^ s) *
        ∫⁻ y in ball (x : V) (r / 2), ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ := by
    intro x _
    rw [← Measure.addHaar_ball_center μ (x : V) (r / 2), ← setLIntegral_const,
      ← lintegral_const_mul' (ENNReal.ofReal (2 ^ s)) _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_ball
    intro y hy
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    exact one_add_norm_rpow_neg_le hs (hmin _ (SetLike.mem_coe.mp x.2.1) (by simpa using x.2.2)) hy
  have hdisj : Set.PairwiseDisjoint (↑t)
      (fun x : ((Λ : Set V) \ {0} : Set V) => ball (x : V) (r / 2)) := by
    intro a _ b _ hab
    show Disjoint (ball (a : V) (r / 2)) (ball (b : V) (r / 2))
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    have hmem : (a : V) - b ∈ Λ :=
      Λ.sub_mem (SetLike.mem_coe.mp a.2.1) (SetLike.mem_coe.mp b.2.1)
    have hne : (a : V) - b ≠ 0 := sub_ne_zero.mpr (fun h => hab (Subtype.ext h))
    linarith [hmin _ hmem hne]
  calc (∑ x ∈ t, ENNReal.ofReal ((1 + ‖(x : V)‖) ^ (-s))) * μ (ball 0 (r / 2))
      = ∑ x ∈ t, ENNReal.ofReal ((1 + ‖(x : V)‖) ^ (-s)) * μ (ball 0 (r / 2)) := by
        rw [Finset.sum_mul]
    _ ≤ ∑ x ∈ t, ENNReal.ofReal (2 ^ s) *
          ∫⁻ y in ball (x : V) (r / 2), ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ :=
        Finset.sum_le_sum hpt
    _ = ENNReal.ofReal (2 ^ s) *
          ∫⁻ y in ⋃ x ∈ t, ball (x : V) (r / 2), ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ := by
        rw [← Finset.mul_sum, lintegral_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
    _ ≤ ENNReal.ofReal (2 ^ s) * ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ :=
        mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) (zero_le)

lemma sum_le_mul_rpow [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    [Nontrivial V] {s : ℝ} (hs : (finrank ℝ V : ℝ) < s) (Λ : AddSubgroup V) {r : ℝ} (hr : 0 < r)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → r ≤ ‖x‖) (t : Finset ((Λ : Set V) \ {0} : Set V)) :
    ∑ x ∈ t, (1 + ‖(x : V)‖) ^ (-s) ≤
      (2 ^ s * (∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ).toReal * 2 ^ finrank ℝ V /
        (μ (ball 0 1)).toReal) * r ^ (-(finrank ℝ V : ℝ)) := by
  have hD0 : (0 : ℝ) ≤ finrank ℝ V := Nat.cast_nonneg _
  have hs0 : 0 ≤ s := by linarith
  have hI : ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ < ∞ := finite_integral_one_add_norm hs
  have hB0 : 0 < μ (ball (0 : V) 1) := measure_ball_pos μ 0 one_pos
  have hBt : μ (ball (0 : V) 1) < ∞ := measure_ball_lt_top
  have hBpos : 0 < (μ (ball (0 : V) 1)).toReal := ENNReal.toReal_pos hB0.ne' hBt.ne
  have h2 := sum_mul_measure_ball_le μ hs0 Λ hr hmin t
  rw [Measure.addHaar_ball μ 0 (by positivity : (0 : ℝ) ≤ r / 2),
    ← ENNReal.ofReal_sum_of_nonneg (fun x _ => by positivity)] at h2
  have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne) h2
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Finset.sum_nonneg (fun x _ => by positivity)),
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at h3
  have e : 2 ^ s * (∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ).toReal * 2 ^ finrank ℝ V /
        (μ (ball 0 1)).toReal * r ^ (-(finrank ℝ V : ℝ)) =
      (2 ^ s * (∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ).toReal) /
        ((r / 2) ^ finrank ℝ V * (μ (ball 0 1)).toReal) := by
    rw [Real.rpow_neg hr.le, Real.rpow_natCast, div_pow]
    field_simp
  rw [e, le_div_iff₀ (mul_pos (pow_pos (by positivity) _) hBpos)]
  linarith [h3]

private lemma rpow_neg_mul_one_add_le_two_mul {D : ℝ} (hD : 1 ≤ D) {r : ℝ} (hr : 0 < r) :
    r ^ (-D) * (1 + r) ≤ 2 * (r ^ (-D) + 1) := by
  have h0 : 0 ≤ r ^ (-D) := by positivity
  rcases le_total r 1 with h | h
  · have : r ^ (-D) * r ≤ r ^ (-D) := mul_le_of_le_one_right h0 h
    nlinarith
  · have h1 : r ^ (-D) * r ≤ 1 := by
      rw [← Real.rpow_add_one hr.ne']
      exact Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)
    have h2 : r ^ (-D) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)
    nlinarith

theorem tsum_one_add_norm_rpow_neg_le (hD : 1 ≤ finrank ℝ V) {M : ℝ}
    (hM : (finrank ℝ V : ℝ) < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : AddSubgroup V) (r : ℝ), 0 < r → (∀ x ∈ Λ, x ≠ 0 → r ≤ ‖x‖) →
      Summable (fun x : ((Λ : Set V) \ {0} : Set V) => (1 + ‖(x : V)‖) ^ (-M)) ∧
      ∑' x : ((Λ : Set V) \ {0} : Set V), (1 + ‖(x : V)‖) ^ (-M) ≤
        C * (r ^ (-(finrank ℝ V : ℝ)) + 1) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by
  let _ : MeasurableSpace V := borel V
  have _ : BorelSpace V := ⟨rfl⟩
  have _ : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hD1 : (1 : ℝ) ≤ (finrank ℝ V : ℝ) := by exact_mod_cast hD
  set s : ℝ := min M ((finrank ℝ V : ℝ) + 1) with hsdef
  have hsD : (finrank ℝ V : ℝ) < s := lt_min hM (by linarith)
  have hsM : s ≤ M := min_le_left _ _
  have hsD1 : s ≤ (finrank ℝ V : ℝ) + 1 := min_le_right _ _
  set K : ℝ := 2 ^ s * (∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂(Measure.addHaar : Measure V)).toReal *
    2 ^ finrank ℝ V / ((Measure.addHaar : Measure V) (ball 0 1)).toReal with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨2 * K + 1, by positivity, fun Λ r hr hmin => ?_⟩
  have hfs : ∀ u : Finset ((Λ : Set V) \ {0} : Set V),
      ∑ x ∈ u, (1 + ‖(x : V)‖) ^ (-s) ≤ K * r ^ (-(finrank ℝ V : ℝ)) :=
    fun u => sum_le_mul_rpow (Measure.addHaar : Measure V) hsD Λ hr hmin u
  have hf0 : ∀ x : ((Λ : Set V) \ {0} : Set V), 0 ≤ (1 + ‖(x : V)‖) ^ (-s) :=
    fun x => by positivity
  have hsum : Summable (fun x : ((Λ : Set V) \ {0} : Set V) => (1 + ‖(x : V)‖) ^ (-s)) :=
    summable_of_sum_le hf0 hfs
  have hle : ∀ x : ((Λ : Set V) \ {0} : Set V),
      (1 + ‖(x : V)‖) ^ (-M) ≤ (1 + ‖(x : V)‖) ^ (-s) * (1 + r) ^ (s - M) := by
    intro x
    have hx : r ≤ ‖(x : V)‖ := hmin _ (SetLike.mem_coe.mp x.2.1) (by simpa using x.2.2)
    have hpos : 0 < 1 + ‖(x : V)‖ := by positivity
    calc (1 + ‖(x : V)‖) ^ (-M) = (1 + ‖(x : V)‖) ^ (-s) * (1 + ‖(x : V)‖) ^ (s - M) := by
          rw [← Real.rpow_add hpos]; congr 1; ring
      _ ≤ (1 + ‖(x : V)‖) ^ (-s) * (1 + r) ^ (s - M) := by
          apply mul_le_mul_of_nonneg_left _ (hf0 x)
          exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have hsumM : Summable (fun x : ((Λ : Set V) \ {0} : Set V) => (1 + ‖(x : V)‖) ^ (-M)) :=
    Summable.of_nonneg_of_le (fun x => by positivity) hle (hsum.mul_right _)
  refine ⟨hsumM, ?_⟩
  have hpow := rpow_neg_mul_one_add_le_two_mul hD1 hr
  have hsplit : (1 + r) ^ (s - M) = (1 + r) ^ (s - finrank ℝ V) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by
    rw [← Real.rpow_add (by linarith)]; congr 1; ring
  have hsD' : (1 + r) ^ (s - finrank ℝ V) ≤ 1 + r := by
    calc (1 + r) ^ (s - finrank ℝ V) ≤ (1 + r) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1 + r := Real.rpow_one _
  have hA : 0 ≤ r ^ (-(finrank ℝ V : ℝ)) := by positivity
  have hB : 0 ≤ (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by positivity
  calc ∑' x : ((Λ : Set V) \ {0} : Set V), (1 + ‖(x : V)‖) ^ (-M)
      ≤ ∑' x : ((Λ : Set V) \ {0} : Set V), (1 + ‖(x : V)‖) ^ (-s) * (1 + r) ^ (s - M) :=
        Summable.tsum_le_tsum hle hsumM (hsum.mul_right _)
    _ = (∑' x : ((Λ : Set V) \ {0} : Set V), (1 + ‖(x : V)‖) ^ (-s)) * (1 + r) ^ (s - M) :=
        tsum_mul_right
    _ ≤ (K * r ^ (-(finrank ℝ V : ℝ))) * (1 + r) ^ (s - M) :=
        mul_le_mul_of_nonneg_right (hsum.tsum_le_of_sum_le hfs) (by positivity)
    _ = K * (r ^ (-(finrank ℝ V : ℝ)) * (1 + r) ^ (s - finrank ℝ V)) *
          (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by rw [hsplit]; ring
    _ ≤ K * (r ^ (-(finrank ℝ V : ℝ)) * (1 + r)) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by
        gcongr
    _ ≤ K * (2 * (r ^ (-(finrank ℝ V : ℝ)) + 1)) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by
        gcongr
    _ ≤ (2 * K + 1) * (r ^ (-(finrank ℝ V : ℝ)) + 1) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by
        nlinarith [mul_nonneg (add_nonneg hA zero_le_one) hB]

theorem tsum_one_add_norm_rpow_neg_le_regimes (hD : 1 ≤ finrank ℝ V) {M : ℝ}
    (hM : (finrank ℝ V : ℝ) < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : AddSubgroup V) (r : ℝ), 0 < r → (∀ x ∈ Λ, x ≠ 0 → r ≤ ‖x‖) →
      Summable (fun x : ((Λ : Set V) \ {0} : Set V) => (1 + ‖(x : V)‖) ^ (-M)) ∧
      (r ≤ 1 → ∑' x : ((Λ : Set V) \ {0} : Set V), (1 + ‖(x : V)‖) ^ (-M) ≤
        C * r ^ (-(finrank ℝ V : ℝ))) ∧
      (1 ≤ r → ∑' x : ((Λ : Set V) \ {0} : Set V), (1 + ‖(x : V)‖) ^ (-M) ≤
        C * r ^ ((finrank ℝ V : ℝ) - M)) := by
  obtain ⟨C, hC, h⟩ := tsum_one_add_norm_rpow_neg_le hD hM
  have hD0 : (0 : ℝ) ≤ finrank ℝ V := Nat.cast_nonneg _
  refine ⟨2 * C, by positivity, fun Λ r hr hmin => ⟨(h Λ r hr hmin).1, fun hr1 => ?_, fun hr1 => ?_⟩⟩
  · have hb := (h Λ r hr hmin).2
    have e1 : (1 + r) ^ ((finrank ℝ V : ℝ) - M) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have e2 : 1 ≤ r ^ (-(finrank ℝ V : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by linarith)
    have e3 : 0 ≤ C * (r ^ (-(finrank ℝ V : ℝ)) + 1) := by positivity
    calc _ ≤ C * (r ^ (-(finrank ℝ V : ℝ)) + 1) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := hb
      _ ≤ C * (r ^ (-(finrank ℝ V : ℝ)) + 1) * 1 := mul_le_mul_of_nonneg_left e1 e3
      _ ≤ 2 * C * r ^ (-(finrank ℝ V : ℝ)) := by nlinarith
  · have hb := (h Λ r hr hmin).2
    have e1 : (1 + r) ^ ((finrank ℝ V : ℝ) - M) ≤ r ^ ((finrank ℝ V : ℝ) - M) :=
      Real.rpow_le_rpow_of_nonpos hr (by linarith) (by linarith)
    have e2 : r ^ (-(finrank ℝ V : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hr1 (by linarith)
    calc _ ≤ C * (r ^ (-(finrank ℝ V : ℝ)) + 1) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := hb
      _ ≤ (C * 2) * r ^ ((finrank ℝ V : ℝ) - M) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC.le) e1 (by positivity)
            (by positivity)
      _ = 2 * C * r ^ ((finrank ℝ V : ℝ) - M) := by ring

end GlobalTheory.LatticeCount
