import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

open Ad3 Ad3.S
open Complex MeasureTheory Filter Asymptotics
open scoped FourierTransform Real

noncomputable section

namespace GlobalTheory.CompanionTheory.HalfWeightKernel

lemma slit_add {y : ℝ} (hy : 0 < y) (x : ℝ) : (y : ℂ) + I * x ∈ slitPlane := by
  rw [mem_slitPlane_iff]; left; simpa using hy

lemma slit_sub {y : ℝ} (hy : 0 < y) (x : ℝ) : (y : ℂ) - I * x ∈ slitPlane := by
  rw [mem_slitPlane_iff]; left; simpa using hy

lemma continuous_KK (α β : ℂ) {y : ℝ} (hy : 0 < y) : Continuous (KK α β y) := by
  unfold KK
  refine Continuous.mul ?_ ?_
  · exact Continuous.cpow (by fun_prop) continuous_const (slit_sub hy)
  · exact Continuous.cpow (by fun_prop) continuous_const (slit_add hy)

lemma norm_KK {α β : ℂ} (h : α.im = β.im) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    ‖KK α β y t‖ = (y ^ 2 + t ^ 2) ^ (-(α + β).re / 2) := by
  have hmem := slit_add hy t
  have hconj : (y : ℂ) - I * t = (starRingEnd ℂ) ((y : ℂ) + I * t) := by
    simp [sub_eq_add_neg]
  unfold KK
  rw [hconj]
  generalize hw : (y : ℂ) + I * t = w at hmem
  have hw0 : w ≠ 0 := slitPlane_ne_zero hmem
  have hcw0 : (starRingEnd ℂ) w ≠ 0 := (map_ne_zero _).2 hw0
  have harg : arg w ≠ π := (mem_slitPlane_iff_arg.1 hmem).1
  have hsq : ‖w‖ ^ 2 = y ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, ← hw]; simp; ring
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  rw [norm_mul, norm_cpow_of_ne_zero hcw0, norm_cpow_of_ne_zero hw0, Complex.arg_conj, if_neg harg,
    Complex.norm_conj, ← hsq, ← Real.rpow_natCast, ← Real.rpow_mul hn.le, div_mul_div_comm,
    ← Real.exp_add, ← Real.rpow_add hn]
  have e : -arg w * (-α).im + arg w * (-β).im = 0 := by simp [h]
  rw [e, Real.exp_zero, div_one]
  congr 1
  simp
  ring

lemma cpow_scale {y : ℝ} (hy : 0 < y) {w : ℂ} (hw : w ≠ 0) (r : ℂ) :
    ((y : ℂ) * w) ^ r = (y : ℂ) ^ r * w ^ r := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hy0 hw), cpow_def_of_ne_zero hy0, cpow_def_of_ne_zero hw,
    ← Complex.exp_add, Complex.log_ofReal_mul hy hw, ofReal_log hy.le]
  congr 1
  ring

lemma KK_scale (α β : ℂ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    KK α β y x = (y : ℂ) ^ (-α - β) * KK α β 1 (x / y) := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  unfold KK
  have e1 : (y : ℂ) - I * x = y * (((1 : ℝ) : ℂ) - I * ((x / y : ℝ) : ℂ)) := by
    push_cast; field_simp
  have e2 : (y : ℂ) + I * x = y * (((1 : ℝ) : ℂ) + I * ((x / y : ℝ) : ℂ)) := by
    push_cast; field_simp
  rw [e1, e2, cpow_scale hy (slitPlane_ne_zero (slit_sub one_pos _)),
    cpow_scale hy (slitPlane_ne_zero (slit_add one_pos _)), sub_eq_add_neg (-α), cpow_add _ _ hy0]
  ring

lemma fourier_KK (α β : ℂ) {y : ℝ} (hy : 0 < y) (ξ : ℝ) :
    𝓕 (KK α β y) ξ = (y : ℂ) ^ (1 - α - β) * Phi α β (ξ * y) := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [Real.fourier_real_eq_integral_exp_smul]
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℂ, G = fun u : ℝ =>
      (y : ℂ) ^ (-α - β) * (KK α β 1 u * ee (-(((ξ * y : ℝ) : ℂ) * u))) := ⟨_, rfl⟩
  have key : ∀ v : ℝ, Complex.exp (((-2 * π * v * ξ : ℝ) : ℂ) * I) • KK α β y v = G (v / y) := by
    intro v
    rw [hG]
    have e : ((-2 * π * v * ξ : ℝ) : ℂ) * I =
        2 * π * I * (-(((ξ * y : ℝ) : ℂ) * ((v / y : ℝ) : ℂ))) := by
      push_cast; field_simp
    simp only [smul_eq_mul]
    rw [KK_scale α β hy v, e, ee]
    ring
  rw [integral_congr_ae (Eventually.of_forall key), Measure.integral_comp_div G y, hG,
    integral_const_mul, abs_of_pos hy, Complex.real_smul,
    show (1 - α - β) = 1 + (-α - β) by ring, cpow_add _ _ hy0, cpow_one]
  unfold Phi
  ring

lemma summable_one_add_sq {σ : ℝ} (hσ : 1 < σ) :
    Summable fun j : ℤ => (1 + (j : ℝ) ^ 2) ^ (-σ / 2) := by
  refine Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow hσ) ?_
  filter_upwards [eventually_cofinite_ne 0] with j hj
  have hj' : (j : ℝ) ≠ 0 := Int.cast_ne_zero.2 hj
  have hpos : 0 < (j : ℝ) ^ 2 := by positivity
  rw [Real.norm_of_nonneg (by positivity)]
  have : |(j : ℝ)| ^ (-σ) = ((j : ℝ) ^ 2) ^ (-σ / 2) := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    push_cast
    ring
  rw [this]
  exact Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith)

lemma unif_bound {σ : ℝ} (hσ : 1 < σ) {y : ℝ} (hy : 0 < y) :
    ∃ g : ℤ → ℝ, Summable g ∧ ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ j : ℤ,
      (y ^ 2 + (r - j) ^ 2) ^ (-σ / 2) ≤ g j := by
  obtain ⟨c, hc0, hc1, hc2⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ y ^ 2 / 3 ∧ c ≤ 1 / 2 :=
    ⟨min (y ^ 2 / 3) (1 / 2), lt_min (by positivity) (by norm_num), min_le_left _ _, min_le_right _ _⟩
  refine ⟨fun j => c ^ (-σ / 2) * (1 + (j : ℝ) ^ 2) ^ (-σ / 2),
    (summable_one_add_sq hσ).mul_left _, ?_⟩
  intro r h0 h1 j
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hj : (j : ℝ) ^ 2 ≤ 2 * (r - j) ^ 2 + 2 := by nlinarith [sq_nonneg (2 * r - j)]
  have hle : c * (1 + (j : ℝ) ^ 2) ≤ y ^ 2 + (r - j) ^ 2 := by
    have h3 : c * (1 + (j : ℝ) ^ 2) ≤ c * (3 + 2 * (r - j) ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hc0.le
    nlinarith [mul_le_mul_of_nonneg_right hc2 (sq_nonneg (r - (j : ℝ)))]
  show _ ≤ c ^ (-σ / 2) * (1 + (j : ℝ) ^ 2) ^ (-σ / 2)
  rw [← Real.mul_rpow hc0.le (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)

lemma decay_KK {α β : ℂ} (h : α.im = β.im) (hσ : 1 < (α + β).re) {y : ℝ} (hy : 0 < y) :
    KK α β y =O[cocompact ℝ] fun x : ℝ => |x| ^ (-(α + β).re) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [(isCompact_singleton (x := (0 : ℝ))).compl_mem_cocompact] with x hx
  have hx0 : x ≠ 0 := hx
  have hpos : 0 < x ^ 2 := by positivity
  have e : |x| ^ (-(α + β).re) = (x ^ 2) ^ (-(α + β).re / 2) := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    push_cast
    ring
  rw [one_mul, Real.norm_of_nonneg (by positivity), norm_KK h hy, e]
  exact Real.rpow_le_rpow_of_nonpos hpos (by nlinarith [sq_nonneg y]) (by linarith)

theorem poisson_kernel : W0 → W2 → P1 := by
  intro _ hW2 s α β a b y hα hβ hσ hy
  have him : α.im = β.im := by simp [hα, hβ]
  obtain ⟨g, hg, hgb⟩ := unif_bound hσ hy
  have hsum : ∀ t : ℝ, (Summable fun j : ℤ => ‖KK α β y (t - j)‖) ∧
      ∑' j : ℤ, ‖KK α β y (t - j)‖ ≤ ∑' j, g j := by
    intro t
    have hle : ∀ j : ℤ, ‖KK α β y (t - j)‖ ≤ g (j - ⌊t⌋) := by
      intro j
      have e : t - j = Int.fract t - ((j - ⌊t⌋ : ℤ) : ℝ) := by
        have := Int.floor_add_fract t
        push_cast
        linarith
      rw [norm_KK him hy, e]
      exact hgb _ (Int.fract_nonneg t) (Int.fract_lt_one t).le _
    have hgs : Summable fun j : ℤ => g (j - ⌊t⌋) := (Equiv.subRight ⌊t⌋).summable_iff.2 hg
    refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hgs, ?_⟩
    calc ∑' j : ℤ, ‖KK α β y (t - j)‖ ≤ ∑' j : ℤ, g (j - ⌊t⌋) :=
          Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hgs) hgs
      _ = ∑' j, g j := (Equiv.subRight ⌊t⌋).tsum_eq g
  have hPhi : Summable fun n : ℤ => ‖Phi α β (n * y)‖ := by
    obtain ⟨Ψ, -, -, h3, h4⟩ := hW2 2 a b
    have hre : (α + β).re = s.re + a + b := by simp [hα, hβ]; ring
    have hs : s ∈ HP (1 - a - b) := by
      show 1 - a - b < s.re
      linarith
    obtain ⟨C, hC⟩ := h4 1 s.re one_pos
    have hsr : 1 - a - b - ((2 : ℕ) : ℝ) + 1 ≤ s.re := by
      have : 1 - a - b < s.re := hs
      push_cast
      linarith
    refine Summable.of_norm_bounded_eventually
      ((Real.summable_abs_int_rpow one_lt_two).mul_left (C * Real.exp (C * s.im ^ 2) / y ^ 2)) ?_
    filter_upwards [eventually_cofinite_ne 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.2 hn
    have hξ : (n : ℝ) * y ≠ 0 := mul_ne_zero hn' hy.ne'
    have hb := hC s (n * y) hξ hsr le_rfl
    rw [h3 s hs _ hξ, ← hα, ← hβ] at hb
    rw [norm_norm]
    refine hb.trans (le_of_eq ?_)
    rw [Real.rpow_neg (abs_nonneg _), Real.rpow_two, abs_mul, abs_of_pos hy, mul_pow]
    have : |(n : ℝ)| ^ 2 ≠ 0 := by positivity
    field_simp
  have hF : ∀ n : ℤ, 𝓕 (KK α β y) (n : ℝ) = (y : ℂ) ^ (1 - α - β) * Phi α β (n * y) :=
    fun n => fourier_KK α β hy n
  have hFs : Summable fun n : ℤ => 𝓕 (KK α β y) (n : ℝ) := by
    simp_rw [hF]
    exact hPhi.of_norm.mul_left _
  refine ⟨⟨∑' j, g j, hsum⟩, hPhi, fun t => ?_⟩
  have P := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable (continuous_KK α β hy) hσ
    (decay_KK him hσ hy) hFs t
  calc ∑' j : ℤ, KK α β y (t - j) = ∑' j : ℤ, KK α β y (t + j) := by
        rw [← (Equiv.neg ℤ).tsum_eq (fun j : ℤ => KK α β y (t + j))]
        refine tsum_congr fun j => ?_
        simp [sub_eq_add_neg]
    _ = ∑' n : ℤ, 𝓕 (KK α β y) (n : ℝ) * fourier n (t : UnitAddCircle) := P
    _ = _ := tsum_congr fun n => by
        rw [hF, fourier_coe_apply, ee]
        congr 2
        push_cast
        ring

end GlobalTheory.CompanionTheory.HalfWeightKernel
