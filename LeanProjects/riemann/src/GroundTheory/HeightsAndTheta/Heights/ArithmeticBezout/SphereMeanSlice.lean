import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMeanVol
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMeanDisc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Set Real

noncomputable section

namespace SphereMean

theorem sqNorm_succ {m : ℕ} (x : Fin (m + 1) → ℂ) :
    sqNorm x = ‖x 0‖ ^ 2 + sqNorm (Fin.tail x) := by
  simp [sqNorm, Fin.sum_univ_succ, Fin.tail]

theorem piFinSuccAbove_zero_apply {m : ℕ} (x : Fin (m + 1) → ℂ) :
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) 0 x = (x 0, Fin.tail x) := by
  simp [MeasurableEquiv.piFinSuccAbove_apply]

theorem lintegral_ballSet_fst (m : ℕ) (φ : ℂ → ENNReal) (hφ : Measurable φ) :
    ∫⁻ x in ballSet (m + 1) 1, φ (x 0) =
      (∫⁻ z : ℂ, (Iio (1 : ℝ)).indicator (fun r => ENNReal.ofReal ((1 - r ^ 2) ^ m)) ‖z‖ * φ z) *
        volume (ballSet m 1) := by
  have he := volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) 0 with he_def
  set A : Set (ℂ × (Fin m → ℂ)) := {p | ‖p.1‖ ^ 2 + sqNorm p.2 < 1} with hA_def
  have hA : MeasurableSet A :=
    measurableSet_lt ((continuous_norm.comp continuous_fst).pow 2 |>.add
      ((continuous_sqNorm m).comp continuous_snd)).measurable measurable_const
  set F : ℂ × (Fin m → ℂ) → ENNReal := A.indicator (fun p => φ p.1) with hF_def
  have hFm : Measurable F := (hφ.comp measurable_fst).indicator hA
  have hF : ∀ x, (ballSet (m + 1) 1).indicator (fun x => φ (x 0)) x = F (e x) := by
    intro x
    rw [he_def, piFinSuccAbove_zero_apply]
    simp only [hF_def, hA_def, indicator, ballSet, mem_ofPred_eq, sqNorm_succ]
  rw [← lintegral_indicator (measurableSet_ballSet _ _)]
  simp_rw [hF]
  rw [he.lintegral_comp_emb e.measurableEmbedding F, Measure.volume_eq_prod,
    lintegral_prod _ hFm.aemeasurable]
  have hm : Measurable (fun z : ℂ =>
      (Iio (1 : ℝ)).indicator (fun r => ENNReal.ofReal ((1 - r ^ 2) ^ m)) ‖z‖ * φ z) :=
    (((ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun r : ℝ => (1 - r ^ 2) ^ m)).indicator
      measurableSet_Iio).comp measurable_norm).mul hφ
  rw [← lintegral_mul_const _ hm]
  · congr 1
    funext z
    have h1 : (fun w => F (z, w)) = (ballSet m (1 - ‖z‖ ^ 2)).indicator (fun _ => φ z) := by
      funext w
      simp only [hF_def, hA_def, indicator, ballSet, mem_ofPred_eq]
      congr 1
      apply propext
      constructor <;> intro h <;> linarith
    have h2 : ∫⁻ w, F (z, w) = φ z * volume (ballSet m (1 - ‖z‖ ^ 2)) := by
      rw [h1]
      exact lintegral_indicator_const (measurableSet_ballSet m _) _
    rw [h2]
    by_cases hz : ‖z‖ < 1
    · have hs : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      rw [volume_ballSet hs]
      simp only [indicator, mem_Iio, hz, ite_true]
      ring
    · have hs : ballSet m (1 - ‖z‖ ^ 2) = ∅ := by
        ext w
        simp only [ballSet, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
        have := sqNorm_nonneg w
        nlinarith [norm_nonneg z]
      rw [hs]
      simp [indicator, hz]

theorem volume_singleton_zero (m : ℕ) : volume ({0} : Set (Fin (m + 1) → ℂ)) = 0 := by
  rw [← Submodule.bot_coe (R := ℝ)]
  exact addHaar_submodule _ _ bot_ne_top

theorem volume_ballSet_succ (m : ℕ) :
    volume (ballSet (m + 1) 1) = ENNReal.ofReal (π / (m + 1)) * volume (ballSet m 1) := by
  have h := lintegral_ballSet_fst m (fun _ => 1) measurable_const
  simp only [setLIntegral_one, mul_one] at h
  rw [h]
  congr 1
  have hp : ∀ z : ℂ, (Iio (1 : ℝ)).indicator (fun r => ENNReal.ofReal ((1 - r ^ 2) ^ m)) ‖z‖ =
      ENNReal.ofReal ((Iio (1 : ℝ)).indicator (fun r => (1 - r ^ 2) ^ m) ‖z‖) := by
    intro z
    by_cases hz : ‖z‖ < 1 <;> simp [indicator, hz]
  simp_rw [hp]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_disc_pow m), integral_disc_pow]
  refine Filter.Eventually.of_forall fun z => ?_
  by_cases hz : ‖z‖ < 1
  · simp only [indicator, mem_Iio, hz, ite_true, Pi.zero_apply]
    have : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
    exact pow_nonneg (by linarith) m
  · simp [indicator, hz]

theorem lintegral_ballSet_neg_log_fst (m : ℕ) :
    ∫⁻ x in ballSet (m + 1) 1, ENNReal.ofReal (-log ‖x 0‖) =
      ENNReal.ofReal (π * harmonic (m + 1) / (2 * (m + 1))) * volume (ballSet m 1) := by
  rw [lintegral_ballSet_fst m (fun z => ENNReal.ofReal (-log ‖z‖))
    (ENNReal.measurable_ofReal.comp (measurable_norm.log.neg))]
  congr 1
  have hp : ∀ z : ℂ, (Iio (1 : ℝ)).indicator (fun r => ENNReal.ofReal ((1 - r ^ 2) ^ m)) ‖z‖ *
      ENNReal.ofReal (-log ‖z‖) =
      ENNReal.ofReal ((Iio (1 : ℝ)).indicator (fun r => -log r * (1 - r ^ 2) ^ m) ‖z‖) := by
    intro z
    by_cases hz : ‖z‖ < 1
    · simp only [indicator, mem_Iio, hz, ite_true]
      rw [ENNReal.ofReal_mul (by linarith [log_nonpos (norm_nonneg z) hz.le]), mul_comm]
    · simp [indicator, hz]
  simp_rw [hp]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_disc_log_pow m), integral_disc_log_pow]
  refine Filter.Eventually.of_forall fun z => ?_
  by_cases hz : ‖z‖ < 1
  · simp only [indicator, mem_Iio, hz, ite_true, Pi.zero_apply]
    have : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
    exact mul_nonneg (by linarith [log_nonpos (norm_nonneg z) hz.le]) (pow_nonneg (by linarith) m)
  · simp [indicator, hz]

theorem sqNorm_pos_of_ne_zero {n : ℕ} {x : Fin n → ℂ} (hx : x ≠ 0) : 0 < sqNorm x := by
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have h1 : ‖x j‖ ^ 2 ≤ sqNorm x :=
    Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : 0 < ‖x j‖ ^ 2 := by positivity
  linarith

theorem lintegral_ballSet_neg_log_sqNorm (m : ℕ) :
    ∫⁻ x in ballSet (m + 1) 1, ENNReal.ofReal (-log (sqNorm x)) =
      ENNReal.ofReal (1 / (m + 1)) * volume (ballSet (m + 1) 1) := by
  set B := ballSet (m + 1) 1 with hB
  have hmeas : Measurable fun x : Fin (m + 1) → ℂ => -log (sqNorm x) :=
    (measurable_sqNorm _).log.neg
  have hnn : 0 ≤ᵐ[volume.restrict B] fun x => -log (sqNorm x) := by
    refine (ae_restrict_iff' (measurableSet_ballSet _ _)).mpr (Filter.Eventually.of_forall ?_)
    intro x hx
    simp only [Pi.zero_apply]
    rw [neg_nonneg]
    exact log_nonpos (sqNorm_nonneg x) (le_of_lt hx)
  rw [lintegral_eq_lintegral_meas_lt _ hnn hmeas.aemeasurable]
  have hlev : ∀ t ∈ Ioi (0 : ℝ), (volume.restrict B) {x | t < -log (sqNorm x)} =
      ENNReal.ofReal (exp (-((m + 1 : ℕ) : ℝ) * t)) * volume B := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    rw [Measure.restrict_apply (measurableSet_lt measurable_const hmeas)]
    have he : exp (-t) < 1 := by
      have := exp_lt_exp.mpr (show -t < 0 by linarith)
      rwa [exp_zero] at this
    have hsub1 : {x | t < -log (sqNorm x)} ∩ B ⊆ ballSet (m + 1) (exp (-t)) := by
      intro x ⟨hx1, _⟩
      simp only [mem_ofPred_eq] at hx1
      have hs : 0 < sqNorm x := by
        rcases (sqNorm_nonneg x).lt_or_eq with h | h
        · exact h
        · rw [← h, log_zero] at hx1; linarith
      simp only [ballSet, mem_ofPred_eq]
      rw [← log_lt_iff_lt_exp hs]
      linarith
    have hsub2 : ballSet (m + 1) (exp (-t)) ⊆ ({x | t < -log (sqNorm x)} ∩ B) ∪ {0} := by
      intro x hx
      by_cases h0 : x = 0
      · exact Or.inr h0
      · left
        have hs := sqNorm_pos_of_ne_zero h0
        simp only [ballSet, mem_ofPred_eq] at hx
        refine ⟨?_, ?_⟩
        · simp only [mem_ofPred_eq]
          have := (log_lt_iff_lt_exp hs).mpr hx
          linarith
        · simp only [hB, ballSet, mem_ofPred_eq]
          linarith
    have heq : volume ({x | t < -log (sqNorm x)} ∩ B) = volume (ballSet (m + 1) (exp (-t))) := by
      refine le_antisymm (measure_mono hsub1) ?_
      refine (measure_mono hsub2).trans ((measure_union_le _ _).trans ?_)
      rw [volume_singleton_zero, add_zero]
    rw [heq, volume_ballSet (exp_pos _), ← exp_nat_mul]
    have : ((m + 1 : ℕ) : ℝ) * -t = -((m + 1 : ℕ) : ℝ) * t := by ring
    rw [this]
  rw [setLIntegral_congr_fun measurableSet_Ioi hlev, lintegral_mul_const _
    (Measurable.ennreal_ofReal (by fun_prop))]
  congr 1
  have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal (exp_neg_integrableOn_Ioi 0 hpos)
    (Filter.Eventually.of_forall fun t => (exp_pos _).le)]
  have := integral_exp_mul_Ioi (a := -((m + 1 : ℕ) : ℝ)) (by linarith) 0
  simp only [mul_zero, exp_zero] at this
  rw [this]
  congr 1
  push_cast
  field_simp

theorem integrableOn_and_integral_of_lintegral {n : ℕ} {B : Set (Fin n → ℂ)}
    (hB : MeasurableSet B) (hBt : volume B ≠ ⊤) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (hnn : ∀ x ∈ B, 0 ≤ f x) {c : ℝ} (hc : 0 ≤ c)
    (h : ∫⁻ x in B, ENNReal.ofReal (f x) = ENNReal.ofReal c * volume B) :
    IntegrableOn f B ∧ ∫ x in B, f x = c * volume.real B := by
  have hnn' : 0 ≤ᵐ[volume.restrict B] f :=
    (ae_restrict_iff' hB).mpr (Filter.Eventually.of_forall hnn)
  refine ⟨⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn').mpr ?_⟩, ?_⟩
  · rw [h]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBt.lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn' hf.aestronglyMeasurable, h, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hc, measureReal_def]

theorem norm_fst_le_one {m : ℕ} {x : Fin (m + 1) → ℂ} (hx : x ∈ ballSet (m + 1) 1) : ‖x 0‖ ≤ 1 := by
  simp only [ballSet, mem_ofPred_eq, sqNorm_succ] at hx
  have := sqNorm_nonneg (Fin.tail x)
  nlinarith [norm_nonneg (x 0)]

theorem integral_ballSet_neg_log_fst (m : ℕ) :
    IntegrableOn (fun x : Fin (m + 1) → ℂ => -log ‖x 0‖) (ballSet (m + 1) 1) ∧
      ∫ x in ballSet (m + 1) 1, -log ‖x 0‖ = harmonic (m + 1) / 2 * volume.real (ballSet (m + 1) 1) := by
  apply integrableOn_and_integral_of_lintegral (measurableSet_ballSet _ _)
    (volume_ballSet_one_ne_top _)
    (f := fun x : Fin (m + 1) → ℂ => -log ‖x 0‖) ((measurable_pi_apply 0).norm.log.neg)
  · intro x hx
    rw [neg_nonneg]
    exact log_nonpos (norm_nonneg _) (norm_fst_le_one hx)
  · exact div_nonneg (by exact_mod_cast (harmonic_pos (Nat.succ_ne_zero m)).le) (by norm_num)
  · rw [lintegral_ballSet_neg_log_fst, volume_ballSet_succ, ← mul_assoc, ← ENNReal.ofReal_mul
      (div_nonneg (by exact_mod_cast (harmonic_pos (Nat.succ_ne_zero m)).le) (by norm_num))]
    congr 2
    field_simp

theorem integral_ballSet_neg_log_sqNorm (m : ℕ) :
    IntegrableOn (fun x : Fin (m + 1) → ℂ => -log (sqNorm x)) (ballSet (m + 1) 1) ∧
      ∫ x in ballSet (m + 1) 1, -log (sqNorm x) = 1 / (m + 1) * volume.real (ballSet (m + 1) 1) :=
  integrableOn_and_integral_of_lintegral (measurableSet_ballSet _ _)
    (volume_ballSet_one_ne_top _) (f := fun x : Fin (m + 1) → ℂ => -log (sqNorm x))
    ((measurable_sqNorm _).log.neg)
    (fun x hx => by
      rw [neg_nonneg]
      exact log_nonpos (sqNorm_nonneg x) (le_of_lt hx))
    (by positivity) (lintegral_ballSet_neg_log_sqNorm m)

end SphereMean

end

end GroundTheory.Heights₂.Heights
