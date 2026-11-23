import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralEqIteratedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumParsevalQExpansionHorizontalLineStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuousStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem lintegral_sq_qs_line (b : ℕ → ℂ) (hb : PolyB b) (y : ℝ) (hy : 0 < y) :
    ∫⁻ x in Set.Ico (0 : ℝ) 1, ENNReal.ofReal (‖qs b (ofComplex (x + y * Complex.I))‖ ^ 2)
      = ∑' n : ℕ, ENNReal.ofReal (‖b n‖ ^ 2 * Real.exp (-4 * π * n * y)) := by
  have him : ∀ x : ℝ, 0 < ((x : ℂ) + y * Complex.I).im := fun x => by simpa using hy
  have hc0 : Continuous fun x : ℝ => ofComplex ((x : ℂ) + y * Complex.I) := by
    have : (fun x : ℝ => ofComplex ((x : ℂ) + y * Complex.I))
        = fun x : ℝ => (⟨(x : ℂ) + y * Complex.I, him x⟩ : ℍ) := by
      funext x; exact ofComplex_apply_of_im_pos (him x)
    rw [this, UpperHalfPlane.isEmbedding_coe.continuous_iff]
    show Continuous fun x : ℝ => (x : ℂ) + y * Complex.I
    fun_prop
  have hc : Continuous fun x : ℝ => ‖qs b (ofComplex (x + y * Complex.I))‖ ^ 2 :=
    ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb).2.comp hc0).norm.pow 2
  have hP := GlobalTheory.T.hasSum_parseval_qExpansion_horizontal_line b b y hb hb hy
  have h1 : (∫ x in (0 : ℝ)..1, conj (qs b (ofComplex (x + y * Complex.I))) * qs b (ofComplex (x + y * Complex.I)))
      = ((∫ x in (0 : ℝ)..1, ‖qs b (ofComplex (x + y * Complex.I))‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    congr 1
    funext x
    rw [Complex.conj_mul']
    push_cast
    rfl
  have h2 : (fun n : ℕ => conj (b n) * b n * (Real.exp (-4 * π * n * y) : ℝ))
      = fun n : ℕ => ((‖b n‖ ^ 2 * Real.exp (-4 * π * n * y) : ℝ) : ℂ) := by
    funext n
    rw [Complex.conj_mul', Complex.ofReal_mul, Complex.ofReal_pow]
  rw [h1, h2, Complex.hasSum_ofReal] at hP
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hP.summable, hP.tsum_eq,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← integral_Ico_eq_integral_Ioo, ofReal_integral_eq_lintegral_ofReal]
  · exact (hc.integrableOn_Icc (a := 0) (b := 1)).mono_set Set.Ico_subset_Icc_self
  · exact Eventually.of_forall fun x => by positivity

theorem lintegral_exp_rpow_le (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∫⁻ y in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (y ^ (a - 1) * Real.exp (-(c * y)))
      ≤ ENNReal.ofReal ((1 / c) ^ a * Real.Gamma a) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hc
  have hpos : 0 < (1 / c) ^ a * Real.Gamma a := mul_pos (by positivity) (Real.Gamma_pos_of_pos ha)
  have hi : Integrable (fun y : ℝ => y ^ (a - 1) * Real.exp (-(c * y))) (volume.restrict (Set.Ioi 0)) :=
    Integrable.of_integral_ne_zero (by rw [h]; exact hpos.ne')
  rw [← h, ofReal_integral_eq_lintegral_ofReal hi]
  · exact lintegral_mono_set Set.Ioo_subset_Ioi_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have : 0 < y := hy
    simp only [Pi.zero_apply]
    positivity

theorem tsum_lintegral_exp_rpow_lt_top (b : ℕ → ℂ) (a : ℝ) (ha0 : 0 < a)
    (hsum : Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ a) :
    ∑' n : ℕ, ENNReal.ofReal (‖b n‖ ^ 2) *
      ∫⁻ y in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (y ^ (a - 1) * Real.exp (-(4 * π * n * y))) < ⊤ := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_, ?_⟩
  · have hi : IntegrableOn (fun y : ℝ => y ^ (a - 1)) (Set.Ioo 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by linarith)).1.mono_set Set.Ioo_subset_Ioc_self
    simpa using hi.lintegral_lt_top
  · have hs1 : Summable fun n : ℕ => ‖b (n + 1)‖ ^ 2 * ((1 / (4 * π * ((n + 1 : ℕ) : ℝ))) ^ a * Real.Gamma a) := by
      refine (((summable_nat_add_iff 1).2 hsum).mul_left ((1 / (4 * π)) ^ a * Real.Gamma a)).congr fun n => ?_
      rw [show 1 / (4 * π * ((n + 1 : ℕ) : ℝ)) = (1 / (4 * π)) / ((n + 1 : ℕ) : ℝ) by field_simp,
        Real.div_rpow (x := 1 / (4 * π)) (by positivity) (by positivity)]
      ring
    have hG0 := Real.Gamma_pos_of_pos ha0
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum (g := fun n : ℕ => ENNReal.ofReal
      (‖b (n + 1)‖ ^ 2 * ((1 / (4 * π * ((n + 1 : ℕ) : ℝ))) ^ a * Real.Gamma a))) fun n => ?_) ?_
    · rw [ENNReal.ofReal_mul (by positivity)]
      gcongr
      exact lintegral_exp_rpow_le a _ ha0 (by positivity)
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs1]
      exact ENNReal.ofReal_lt_top

theorem integrableOn_sq_qs_low : ∀ (e : ℕ) (b : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → PolyB b →
    (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) →
    IntegrableOn (fun τ : ℍ => ‖qs b τ‖ ^ 2 * τ.im ^ (2 * (e : ℝ) + s)) {τ | τ ∈ strip ∧ τ.im < 1} := by
  intro e b s he hs hb hsum
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  set a : ℝ := 2 * (e : ℝ) - 1 + s with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have hp : 2 * (e : ℝ) + s = a + 1 := by rw [ha]; ring
  rw [hp]
  have hcont : Continuous fun τ : ℍ => ‖qs b τ‖ ^ 2 * τ.im ^ (a + 1) :=
    ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb).2.norm.pow 2).mul
      (UpperHalfPlane.continuous_im.rpow_const fun τ => Or.inr (by linarith))
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  have hmeas : MeasurableSet {τ : ℍ | τ.im < 1} :=
    (isOpen_lt UpperHalfPlane.continuous_im continuous_const).measurableSet
  set G : ℍ → ENNReal := fun τ => ENNReal.ofReal (‖qs b τ‖ ^ 2 * τ.im ^ (a + 1)) with hG
  have hGm : Measurable G := ENNReal.measurable_ofReal.comp hcont.measurable
  have e1 : ∫⁻ τ in {τ : ℍ | τ ∈ strip ∧ τ.im < 1}, ‖‖qs b τ‖ ^ 2 * τ.im ^ (a + 1)‖ₑ
      = ∫⁻ τ in strip, Set.indicator {τ : ℍ | τ.im < 1} G τ := by
    rw [lintegral_indicator hmeas, Measure.restrict_restrict hmeas]
    have : {τ : ℍ | τ ∈ strip ∧ τ.im < 1} = {τ : ℍ | τ.im < 1} ∩ strip := by
      ext τ; simp [and_comm]
    rw [this]
    refine lintegral_congr fun τ => ?_
    have := τ.im_pos
    exact Real.enorm_of_nonneg (by positivity)
  rw [hasFiniteIntegral_iff_enorm, e1, GlobalTheory.T.unitStrip_integral_eq_iterated.1 _ (hGm.indicator hmeas)]
  set T : ℕ → ℝ → ENNReal := fun n y =>
    ENNReal.ofReal (‖b n‖ ^ 2) * ENNReal.ofReal (y ^ (a - 1) * Real.exp (-(4 * π * n * y))) with hT
  have hTm : ∀ n : ℕ, Measurable fun y : ℝ => ENNReal.ofReal (y ^ (a - 1) * Real.exp (-(4 * π * n * y))) := fun n => by
    refine ENNReal.measurable_ofReal.comp ?_
    fun_prop
  have e2 : ∀ y ∈ Set.Ioi (0 : ℝ),
      (∫⁻ x in Set.Ico (0 : ℝ) 1, Set.indicator {τ : ℍ | τ.im < 1} G (ofComplex (x + y * Complex.I)))
        * ENNReal.ofReal (1 / y ^ 2) = Set.indicator (Set.Iio 1) (fun y => ∑' n, T n y) y := by
    intro y hy
    have hy : 0 < y := hy
    have him : ∀ x : ℝ, (ofComplex ((x : ℂ) + y * Complex.I)).im = y := fun x => by
      have h : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy
      rw [ofComplex_apply_of_im_pos h]
      show ((x : ℂ) + y * Complex.I).im = y
      simp
    by_cases h1 : y < 1
    · have : ∀ x : ℝ, Set.indicator {τ : ℍ | τ.im < 1} G (ofComplex (x + y * Complex.I))
          = ENNReal.ofReal (‖qs b (ofComplex (x + y * Complex.I))‖ ^ 2) * ENNReal.ofReal (y ^ (a + 1)) := fun x => by
        rw [Set.indicator_of_mem (by simpa [him x] using h1), hG]
        simp only [him x]
        rw [ENNReal.ofReal_mul (by positivity)]
      simp only [this]
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_sq_qs_line b hb y hy,
        Set.indicator_of_mem (by simpa using h1), mul_assoc, ← ENNReal.tsum_mul_right]
      refine tsum_congr fun n => ?_
      simp only [hT]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have : y ^ (a + 1) = y ^ (a - 1) * y ^ 2 := by
        rw [← Real.rpow_two, ← Real.rpow_add hy]; congr 1; ring
      rw [this, show -4 * π * n * y = -(4 * π * n * y) by ring]
      field_simp
    · have : ∀ x : ℝ, Set.indicator {τ : ℍ | τ.im < 1} G (ofComplex (x + y * Complex.I)) = 0 := fun x =>
        Set.indicator_of_notMem (by simpa [him x] using h1) _
      simp only [this]
      rw [Set.indicator_of_notMem (by simpa using h1)]
      simp
  rw [setLIntegral_congr_fun measurableSet_Ioi e2, lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Set.inter_comm, Set.Ioi_inter_Iio,
    lintegral_tsum (f := T) fun n => ((hTm n).const_mul _).aemeasurable]
  simp only [hT, lintegral_const_mul _ (hTm _)]
  exact tsum_lintegral_exp_rpow_lt_top b a ha0 hsum

end GlobalTheory.EisM
